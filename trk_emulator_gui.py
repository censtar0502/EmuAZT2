#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Мультипротокольный Эмулятор ТРК
Поддерживаемые протоколы:
  - АЗТ v2.0      (RS-485, 4800 бод, 7E2)
  - GasKitLink v1.2 (RS-422, 9600 бод, 8N1)

Сборка EXE:
  pip install pyinstaller pyserial
  pyinstaller --onefile --windowed --name TRK_Emulator trk_emulator_gui.py
"""

import sys
import threading
import time
import queue
import tkinter as tk
from tkinter import ttk, messagebox

try:
    import serial
    import serial.tools.list_ports
    HAS_SERIAL = True
except ImportError:
    HAS_SERIAL = False

DISPENSE_LPM = 50.0   # скорость отпуска л/мин (общая для обоих протоколов)

# ═══════════════════════════════════════════════════════════════════════════════
#  АЗТ v2.0 — КОНСТАНТЫ И ФУНКЦИИ
# ═══════════════════════════════════════════════════════════════════════════════

DEL = 0x7F; STX = 0x02; ETX = 0x03; ACK = 0x06; NAK = 0x15; CAN = 0x18

CMD_STATUS       = 0x31;  CMD_AUTHORIZE    = 0x32;  CMD_RESET        = 0x33
CMD_CUR_DATA     = 0x34;  CMD_FULL_DATA    = 0x35;  CMD_TOTALIZERS   = 0x36
CMD_TYPE         = 0x37;  CMD_CONFIRM      = 0x38;  CMD_VERSION      = 0x50
CMD_SET_PRICE    = 0x51;  CMD_SET_CUTOFF   = 0x52;  CMD_SET_DOSE_RUB = 0x53
CMD_SET_DOSE_LIT = 0x54;  CMD_TOPOFF       = 0x55;  CMD_FORCE_START  = 0x56
CMD_SET_NET_NUM  = 0x5D;  CMD_SET_COMMON   = 0x57;  CMD_TRANSACTION  = 0x59
CMD_READ_PARAMS  = 0x4E;  CMD_WRITE_PARAMS = 0x4F;  CMD_READ_DOSE    = 0x58

CMD_NAMES = {
    CMD_STATUS:'STATUS', CMD_AUTHORIZE:'AUTHORIZE', CMD_RESET:'RESET',
    CMD_CUR_DATA:'CUR_DATA', CMD_FULL_DATA:'FULL_DATA',
    CMD_TOTALIZERS:'TOTALIZERS', CMD_TYPE:'TYPE', CMD_CONFIRM:'CONFIRM',
    CMD_VERSION:'VERSION', CMD_SET_PRICE:'SET_PRICE',
    CMD_SET_CUTOFF:'SET_CUTOFF', CMD_SET_DOSE_RUB:'SET_DOSE_RUB',
    CMD_SET_DOSE_LIT:'SET_DOSE_LIT', CMD_TOPOFF:'TOPOFF',
    CMD_FORCE_START:'FORCE_START', CMD_SET_NET_NUM:'SET_NET_NUM',
    CMD_SET_COMMON:'SET_COMMON', CMD_TRANSACTION:'TRANSACTION',
    CMD_READ_PARAMS:'READ_PARAMS', CMD_WRITE_PARAMS:'WRITE_PARAMS',
    CMD_READ_DOSE:'READ_DOSE',
}

ST_OFF_RK_IN  = 0x30;  ST_OFF_RK_OUT = 0x31;  ST_AUTHORIZED = 0x32
ST_DISPENSING = 0x33;  ST_DONE       = 0x34;  ST_BMU_DOSE   = 0x38
CAUSE_NORMAL  = 0x30;  CAUSE_OVERFLOW = 0x31
AZT_VERSION   = '00000002'
TRK_IDENTIFIER = 0x3B

START_BYTE_OFFSETS = {0x02: 0}
for _b in range(0x07, 0x15):
    START_BYTE_OFFSETS[_b] = (_b - 0x06) * 15


def _compl(b: int) -> int:
    return b ^ 0x7F

def _checksum(normal_bytes) -> int:
    cs = 0
    for b in normal_bytes: cs ^= b
    cs ^= ETX; cs |= 0x40; return cs

def _short(code: int) -> bytes:
    return bytes([DEL, code])

def _data_resp(data: list) -> bytes:
    body = []
    for b in data: body += [b, _compl(b)]
    return bytes([DEL, STX] + body + [ETX, ETX, _checksum(data)])

def _lit_str(liters: float, d: int) -> str:
    return str(int(round(liters * 100))).zfill(d)

def _rub_str(rubles: float, d: int) -> str:
    return str(int(round(rubles * 100))).zfill(d)


# ═══════════════════════════════════════════════════════════════════════════════
#  АЗТ v2.0 — СОСТОЯНИЕ ТРК
# ═══════════════════════════════════════════════════════════════════════════════

class AZTState:
    def __init__(self, net_addr: int = 1):
        self.net_addr    = net_addr
        self.status      = ST_OFF_RK_IN
        self.cause       = CAUSE_NORMAL
        self.rk_in       = True
        self.price_kop   = 4500
        self.preset_lit  = 0.0
        self.preset_rub  = 0.0
        self.preset_mode = 'L'
        self.cur_liters  = 0.0
        self.full_liters = 0.0
        self.full_rubles = 0.0
        self.total_liters = 12345.67
        self.total_rubles = 617283.15
        self.transaction  = 1
        self.id_number    = '12345'
        self.fw_version   = '100'
        self.cutoff_thr   = 0.50
        self._dispensing  = False
        self._disp_thread = None
        self._lock        = threading.Lock()
        self.on_done      = None

    def start_dispensing(self):
        if self._dispensing: return
        self._dispensing = True
        def _worker():
            price = self.price_kop / 100.0
            if self.preset_mode == 'L' and self.preset_lit > 0:
                target = self.preset_lit
            elif self.preset_mode == 'R' and self.preset_rub > 0 and price > 0:
                target = self.preset_rub / price
            else:
                target = 9999.0
            rate = DISPENSE_LPM / 60.0; interval = 0.1; step = rate * interval
            while self._dispensing:
                time.sleep(interval)
                if not self._dispensing: break
                delta = min(step, target - self.full_liters)
                if delta <= 0: break
                with self._lock:
                    self.cur_liters  += delta
                    self.full_liters += delta
                    self.full_rubles  = self.full_liters * price
                    self.total_liters += delta
                    self.total_rubles += delta * price
            if self._dispensing:
                self._dispensing = False
                with self._lock:
                    self.status = ST_DONE; self.cause = CAUSE_NORMAL
                if self.on_done: self.on_done('dose')
        self._disp_thread = threading.Thread(target=_worker, daemon=True)
        self._disp_thread.start()

    def stop_dispensing(self):
        if not self._dispensing: return
        self._dispensing = False
        with self._lock:
            self.status = ST_DONE; self.cause = CAUSE_NORMAL
        if self.on_done: self.on_done('manual')

    def price_str(self, d=6)      -> str: return str(self.price_kop).zfill(d)
    def cur_str(self)             -> str: return _lit_str(self.cur_liters, 5)
    def full_lit_str(self)        -> str: return _lit_str(self.full_liters, 6)
    def full_rub_str(self)        -> str: return _rub_str(self.full_rubles, 8)
    def total_lit_str(self, d=10) -> str: return _lit_str(self.total_liters, d)
    def total_rub_str(self, d=10) -> str: return _rub_str(self.total_rubles, d)
    def preset_str(self)          -> str: return _lit_str(self.preset_lit, 5)


# ═══════════════════════════════════════════════════════════════════════════════
#  АЗТ v2.0 — ОБРАБОТЧИК КОМАНД
# ═══════════════════════════════════════════════════════════════════════════════

class AZTPacketProcessor:
    def __init__(self, trk: AZTState, log_cb=None, state_cb=None):
        self.trk       = trk
        self._log_cb   = log_cb
        self._state_cb = state_cb

    def _log(self, msg):
        if self._log_cb: self._log_cb(msg)

    def _notify(self):
        if self._state_cb: self._state_cb()

    def feed(self, buf: bytearray):
        while buf:
            result = self._try_one(buf)
            if result is None: break
            consumed, resp = result
            del buf[:consumed]
            if resp is not None: return resp
        return None

    def _try_one(self, buf: bytearray):
        i = 0
        while i < len(buf) and buf[i] != DEL: i += 1
        if i >= len(buf): return len(buf), None
        if i > 0: return i, None
        if len(buf) < 3: return None
        start_byte = buf[1]
        if start_byte not in START_BYTE_OFFSETS: return 1, None
        offset = START_BYTE_OFFSETS[start_byte]
        third  = buf[2]
        if 0x21 <= third <= 0x2F:
            return self._parse_v1(buf, offset)
        elif 0x30 < third <= 0x5E:
            return self._parse_v2(buf)
        else:
            return 2, None

    def _find_end(self, buf, from_pos):
        i = from_pos
        while i + 2 < len(buf):
            if buf[i] == ETX and buf[i+1] == ETX: return i + 3
            i += 1
        return -1

    def _extract_data(self, buf, from_pos, end_pos):
        section = buf[from_pos:end_pos - 3]
        data, i = [], 0
        while i + 1 < len(section):
            b, bc = section[i], section[i+1]
            if _compl(b) != bc: return data, False
            data.append(b); i += 2
        return data, True

    def _parse_v1(self, buf, offset):
        if len(buf) < 6: return None
        na, na_c = buf[2], buf[3]; cmd, cmd_c = buf[4], buf[5]
        if _compl(na) != na_c or _compl(cmd) != cmd_c: return 2, None
        net_addr = (na - 0x20) + offset
        end = self._find_end(buf, 6)
        if end < 0: return None
        data, ok = self._extract_data(buf, 6, end)
        if not ok: return end, None
        if _checksum([na, cmd] + data) != buf[end-1]:
            self._log(f'  [CS ERR] {bytes(buf[:end]).hex(" ").upper()}')
            return end, None
        cname = CMD_NAMES.get(cmd, f'0x{cmd:02X}')
        self._log(f'RX  addr={net_addr}  {cname}')
        if net_addr != self.trk.net_addr: return end, b''
        return end, self._dispatch(cmd, data)

    def _parse_v2(self, buf):
        if len(buf) < 4: return None
        cmd, cmd_c = buf[2], buf[3]
        if _compl(cmd) != cmd_c: return 2, None
        end = self._find_end(buf, 4)
        if end < 0: return None
        data, ok = self._extract_data(buf, 4, end)
        if not ok: return end, None
        if _checksum([cmd] + data) != buf[end-1]: return end, None
        cname = CMD_NAMES.get(cmd, f'0x{cmd:02X}')
        self._log(f'RX  broadcast  {cname}')
        return end, self._dispatch(cmd, data)

    def _dispatch(self, cmd, data, broadcast=False):
        trk = self.trk
        if cmd == CMD_STATUS:
            resp = [trk.status]
            if trk.status == ST_DONE: resp.append(trk.cause)
            self._log(f'  → STATUS {trk.status:02X}' +
                      (f'+{trk.cause:02X}' if trk.status == ST_DONE else ''))
            return _data_resp(resp)

        elif cmd == CMD_AUTHORIZE:
            if trk.status in (ST_OFF_RK_IN, ST_OFF_RK_OUT, ST_BMU_DOSE):
                trk.status = ST_AUTHORIZED; trk.transaction += 1
                trk.full_liters = 0.0; trk.full_rubles = 0.0; trk.cur_liters = 0.0
                self._log(f'  → AUTHORIZED txn#{trk.transaction}'); self._notify()
                return _short(ACK)
            return _short(CAN)

        elif cmd == CMD_RESET:
            if trk.status in (ST_AUTHORIZED, ST_DISPENSING):
                if trk.status == ST_DISPENSING: trk.stop_dispensing()
                trk.status = (ST_DONE if trk.full_liters > 0
                              else (ST_OFF_RK_IN if trk.rk_in else ST_OFF_RK_OUT))
                self._notify(); return _short(ACK)
            elif trk.status == ST_BMU_DOSE:
                trk.preset_lit = 0.0
                trk.status = ST_OFF_RK_IN if trk.rk_in else ST_OFF_RK_OUT
                self._notify(); return _short(ACK)
            return _short(CAN)

        elif cmd == CMD_CUR_DATA:
            with trk._lock: s = trk.cur_str()
            return _data_resp([0x30] + [ord(c) for c in s])

        elif cmd == CMD_FULL_DATA:
            with trk._lock:
                lit = trk.full_lit_str(); cost = trk.full_rub_str(); pr = trk.price_str()
            return _data_resp([ord(c) for c in lit + cost + pr])

        elif cmd == CMD_TOTALIZERS:
            with trk._lock: tl = trk.total_lit_str(); tr = trk.total_rub_str()
            return _data_resp([ord(c) for c in tl + tr])

        elif cmd == CMD_TYPE:
            return _data_resp([TRK_IDENTIFIER])

        elif cmd == CMD_CONFIRM:
            if trk.status == ST_DONE:
                trk.status = ST_OFF_RK_IN if trk.rk_in else ST_OFF_RK_OUT
                self._log('  → IDLE after confirm'); self._notify()
                return _short(ACK)
            return _short(CAN)

        elif cmd == CMD_VERSION:
            return _data_resp([ord(c) for c in AZT_VERSION])

        elif cmd == CMD_SET_PRICE:
            if trk.status in (ST_OFF_RK_IN, ST_OFF_RK_OUT) and len(data) >= 4:
                try:
                    trk.price_kop = int(''.join(chr(b) for b in data[:4]))
                    trk.full_liters = 0.0; trk.full_rubles = 0.0; trk.transaction += 1
                    self._log(f'  price={trk.price_kop/100:.2f}'); self._notify()
                    return _short(ACK)
                except Exception: pass
            return _short(CAN)

        elif cmd == CMD_SET_CUTOFF:
            if trk.status in (ST_OFF_RK_IN, ST_OFF_RK_OUT) and len(data) >= 3:
                s = ''.join(chr(b) for b in data[:3])
                trk.cutoff_thr = int(s[0]) + int(s[1])*0.1 + int(s[2])*0.01
                return _short(ACK)
            return _short(CAN)

        elif cmd == CMD_SET_DOSE_RUB:
            if trk.status in (ST_OFF_RK_IN, ST_OFF_RK_OUT) and len(data) >= 6:
                try:
                    trk.preset_rub  = int(''.join(chr(b) for b in data[:6])) / 100.0
                    trk.preset_mode = 'R'
                    trk.preset_lit  = (trk.preset_rub / (trk.price_kop/100.0)
                                       if trk.price_kop else 0.0)
                    self._log(f'  dose={trk.preset_rub:.2f}rub={trk.preset_lit:.2f}L')
                    self._notify(); return _short(ACK)
                except Exception: pass
            return _short(CAN)

        elif cmd == CMD_SET_DOSE_LIT:
            if trk.status in (ST_OFF_RK_IN, ST_OFF_RK_OUT) and len(data) >= 5:
                try:
                    trk.preset_lit  = int(''.join(chr(b) for b in data[:5])) / 100.0
                    trk.preset_mode = 'L'
                    trk.preset_rub  = trk.preset_lit * (trk.price_kop / 100.0)
                    self._log(f'  dose={trk.preset_lit:.2f}L={trk.preset_rub:.2f}rub')
                    self._notify(); return _short(ACK)
                except Exception: pass
            return _short(CAN)

        elif cmd == CMD_TOPOFF:
            if trk.status in (ST_OFF_RK_IN, ST_OFF_RK_OUT): return _short(ACK)
            return _short(CAN)

        elif cmd == CMD_FORCE_START:
            if trk.status == ST_AUTHORIZED:
                trk.status = ST_DISPENSING; trk.rk_in = False
                trk.start_dispensing(); self._notify()
                return _short(ACK)
            return _short(CAN)

        elif cmd == CMD_SET_NET_NUM:
            if len(data) >= 8:
                net_s = ''.join(chr(b) for b in data[5:8])
                if net_s == '000':
                    return _data_resp([ord(c) for c in str(trk.net_addr).zfill(3)] + [0x31])
            return _short(ACK)

        elif cmd == CMD_SET_COMMON:
            if len(data) >= 2 and data[0] == 0x31 and data[1] == 0x3F:
                return _data_resp([ord(c) for c in trk.id_number])
            return b''

        elif cmd == CMD_TRANSACTION:
            return _data_resp([ord(c) for c in str(trk.transaction).zfill(8)])

        elif cmd == CMD_READ_PARAMS:
            if len(data) == 0:
                return _data_resp([0x30, 0x31, 0x33, 0x34, 0x43])
            resp = []
            for p in data:
                if p == 0x30: resp += [p, 0x31]
                elif p == 0x31: resp += [p, 0x31]
                elif p == 0x43: resp += [p] + [ord(c) for c in trk.fw_version]
            return _data_resp(resp) if resp else _short(NAK)

        elif cmd == CMD_WRITE_PARAMS:
            if trk.status in (ST_OFF_RK_IN, ST_OFF_RK_OUT): return _short(ACK)
            return _short(CAN)

        elif cmd == CMD_READ_DOSE:
            if trk.status in (ST_OFF_RK_IN, ST_OFF_RK_OUT, ST_BMU_DOSE):
                if trk.preset_lit > 0:
                    return _data_resp([0x30] + [ord(c) for c in trk.preset_str()])
            return _short(CAN)

        else:
            return _short(NAK)


# ═══════════════════════════════════════════════════════════════════════════════
#  GASKIT v1.2 — КОНСТАНТЫ
# ═══════════════════════════════════════════════════════════════════════════════

GK_STX      = 0x02
GK_ADDR_HI  = 0x00
GK_ADDR_LO  = 0x01

GK_IDLE          = 1   # Ожидание
GK_CALLING       = 2   # Пистолет поднят без авторизации
GK_AUTHORIZED    = 3   # Авторизовано, ожидание подъёма пистолета
GK_STARTED       = 4   # Пистолет поднят, запуск насоса
GK_SUSP_STARTED  = 5   # Заморожен во время запуска
GK_FUELLING      = 6   # Отпуск топлива
GK_SUSP_FUELLING = 7   # Приостановлен во время отпуска
GK_STOPPED       = 8   # Отпуск завершён (доза или стоп)
GK_END_TXN       = 9   # Пистолет повешен, ожидание команды N

# Ожидаемая длина payload (в байтах) для каждой команды
GK_CMD_PAYLOAD_LEN = {
    ord('S'): 1,   ord('V'): 14,  ord('M'): 14,
    ord('L'): 1,   ord('R'): 1,   ord('T'): 1,
    ord('C'): 2,   ord('N'): 1,   ord('B'): 1,
    ord('G'): 1,   ord('W'): 7,   ord('Z'): 3,
    ord('D'): 3,
}


def gk_build(payload) -> bytes:
    """Собрать GasKit фрейм: [0x02][0x00][0x01][payload...][CRC]
    CRC = XOR(frame[1:-1]) = XOR(addrHi, addrLo, payload_bytes)
    """
    if isinstance(payload, str):
        payload = payload.encode('latin-1')
    frame = bytes([GK_STX, GK_ADDR_HI, GK_ADDR_LO]) + payload
    crc = 0
    for b in frame[1:]: crc ^= b
    return frame + bytes([crc])


# ═══════════════════════════════════════════════════════════════════════════════
#  GASKIT v1.2 — СОСТОЯНИЕ ТРК
# ═══════════════════════════════════════════════════════════════════════════════

class GasKitState:
    def __init__(self):
        self.nozzle      = 1           # номер пистолета
        self.gk_state    = GK_IDLE     # текущее состояние (1–9)
        self.txn_id      = 'a'         # ID транзакции 'a'…'z'
        self.price_kop   = 4500        # цена копейки/л (4500 = 45.00 руб/л)
        self.preset_cl   = 0           # объём дозы в сантилитрах
        self.preset_kop  = 0           # денежная доза в копейках
        self.preset_mode = 'V'         # 'V' = объём, 'M' = деньги
        self.cur_cl      = 0.0         # текущий объём транзакции (cl)
        self.cur_kop     = 0.0         # текущая стоимость (копейки)
        self.total_cl    = 396003.0    # суммарник (сантилитры)
        self._dispensing  = False
        self._disp_thread = None
        self._lock        = threading.Lock()
        self.on_done      = None

    def advance_txn_id(self):
        """Перейти к следующему ID транзакции."""
        self.txn_id = chr(ord(self.txn_id) + 1) if self.txn_id < 'z' else 'a'

    def start_dispensing(self):
        if self._dispensing: return
        self._dispensing = True
        def _worker():
            # Краткая задержка перед началом → переход в GK_FUELLING
            time.sleep(0.4)
            with self._lock:
                if self.gk_state == GK_STARTED:
                    self.gk_state = GK_FUELLING

            rate     = DISPENSE_LPM / 60.0   # л/с
            interval = 0.1
            step_cl  = rate * interval * 100  # сантилитры за интервал

            if self.preset_mode == 'V' and self.preset_cl > 0:
                target_cl = float(self.preset_cl)
            elif self.preset_mode == 'M' and self.preset_kop > 0 and self.price_kop > 0:
                target_cl = float(self.preset_kop * 100) / self.price_kop
            else:
                target_cl = 999900.0   # безлимитно

            while self._dispensing:
                time.sleep(interval)
                if not self._dispensing: break
                delta = min(step_cl, target_cl - self.cur_cl)
                if delta <= 0: break
                with self._lock:
                    self.cur_cl   += delta
                    self.cur_kop   = self.cur_cl * self.price_kop / 100.0
                    self.total_cl += delta

            if self._dispensing:
                self._dispensing = False
                with self._lock:
                    self.gk_state = GK_STOPPED
                if self.on_done: self.on_done('dose')

        self._disp_thread = threading.Thread(target=_worker, daemon=True)
        self._disp_thread.start()

    def stop_dispensing(self):
        if not self._dispensing: return
        self._dispensing = False
        with self._lock:
            self.gk_state = GK_STOPPED
        if self.on_done: self.on_done('manual')

    def state_str(self) -> str:
        # nozzle=0 когда пистолет в кронштейне (IDLE или END_TXN)
        nozzle = 0 if self.gk_state in (GK_IDLE, GK_END_TXN) else self.nozzle
        return f'S{self.gk_state}{nozzle}'


# ═══════════════════════════════════════════════════════════════════════════════
#  GASKIT v1.2 — ОБРАБОТЧИК КОМАНД
# ═══════════════════════════════════════════════════════════════════════════════

class GasKitPacketProcessor:
    def __init__(self, trk: GasKitState, log_cb=None, state_cb=None):
        self.trk       = trk
        self._log_cb   = log_cb
        self._state_cb = state_cb

    def _log(self, msg):
        if self._log_cb: self._log_cb(msg)

    def _notify(self):
        if self._state_cb: self._state_cb()

    def feed(self, buf: bytearray):
        while buf:
            result = self._try_one(buf)
            if result is None: break
            consumed, resp = result
            del buf[:consumed]
            if resp is not None: return resp
        return None

    def _try_one(self, buf: bytearray):
        if len(buf) < 3: return None

        # Ищем преамбулу [0x02][0x00][0x01]
        found = False
        for i in range(len(buf) - 2):
            if buf[i] == GK_STX and buf[i+1] == GK_ADDR_HI and buf[i+2] == GK_ADDR_LO:
                found = True
                break

        if not found:
            return max(1, len(buf) - 2), None

        if i > 0:
            return i, None   # пропустить мусор перед фреймом

        # buf[0..2] = [STX][0x00][0x01]
        if len(buf) < 5: return None

        cmd_byte = buf[3]
        if cmd_byte not in GK_CMD_PAYLOAD_LEN:
            self._log(f'  [GK UNKNOWN CMD] 0x{cmd_byte:02X}')
            return 4, None

        frame_len = 4 + GK_CMD_PAYLOAD_LEN[cmd_byte]  # STX+addr2+payload+CRC
        if len(buf) < frame_len: return None

        frame = bytes(buf[:frame_len])
        # Проверка CRC = XOR(frame[1:-1])
        crc = 0
        for b in frame[1:-1]: crc ^= b
        if crc != frame[-1]:
            self._log(f'  [GK CRC ERR] {frame.hex(" ").upper()}')
            return frame_len, None

        payload = frame[3:-1]
        self._log(f'RX  {frame.hex(" ").upper()}  | "{payload.decode("latin-1", errors="replace")}"')
        return frame_len, self._dispatch(payload)

    def _dispatch(self, payload: bytes):
        trk = self.trk
        cmd = chr(payload[0])

        if cmd == 'S':
            s = trk.state_str()
            self._log(f'  → {s}')
            return gk_build(s)

        elif cmd == 'V':
            # V{nozzle};{volume_cl:06d};{price_kop:04d}
            try:
                parts = payload[1:].decode('ascii').split(';')
                vol_cl = int(parts[1])
                price  = int(parts[2])
            except Exception as e:
                self._log(f'  [GK V ERR] {e}')
                return gk_build(trk.state_str())
            if trk.gk_state == GK_IDLE:
                trk.preset_cl   = vol_cl
                trk.preset_mode = 'V'
                trk.price_kop   = price
                trk.cur_cl      = 0.0
                trk.cur_kop     = 0.0
                trk.gk_state    = GK_AUTHORIZED
                self._notify()
            s = trk.state_str()
            self._log(f'  → {s}  vol={vol_cl}cl price={price}')
            return gk_build(s)

        elif cmd == 'M':
            # M{nozzle};{money_kop:06d};{price_kop:04d}
            try:
                parts = payload[1:].decode('ascii').split(';')
                money = int(parts[1])
                price = int(parts[2])
            except Exception as e:
                self._log(f'  [GK M ERR] {e}')
                return gk_build(trk.state_str())
            if trk.gk_state == GK_IDLE:
                trk.preset_kop  = money
                trk.price_kop   = price
                trk.preset_cl   = int(money * 100 / price) if price else 0
                trk.preset_mode = 'M'
                trk.cur_cl      = 0.0
                trk.cur_kop     = 0.0
                trk.gk_state    = GK_AUTHORIZED
                self._notify()
            s = trk.state_str()
            self._log(f'  → {s}  money={money}kop price={price}')
            return gk_build(s)

        elif cmd == 'L':
            with trk._lock: cl = int(round(trk.cur_cl))
            s = f'L{trk.nozzle}{trk.txn_id}{trk.gk_state};{cl:06d}'
            self._log(f'  → {s}')
            return gk_build(s)

        elif cmd == 'R':
            with trk._lock: kop = int(round(trk.cur_kop))
            s = f'R{trk.nozzle}{trk.txn_id}{trk.gk_state};{kop:06d}'
            self._log(f'  → {s}')
            return gk_build(s)

        elif cmd == 'T':
            with trk._lock:
                cl  = int(round(trk.cur_cl))
                kop = int(round(trk.cur_kop))
            s = (f'T{trk.nozzle}{trk.txn_id}{trk.gk_state}'
                 f';{kop:06d};{cl:06d};{trk.price_kop:04d}')
            self._log(f'  → {s}')
            return gk_build(s)

        elif cmd == 'C':
            # Cg — суммарник по пистолету g
            with trk._lock: total = int(round(trk.total_cl))
            s = f'C{trk.nozzle};{total:09d}'
            self._log(f'  → {s}')
            return gk_build(s)

        elif cmd == 'N':
            # Конец транзакции
            s = trk.state_str()
            if trk.gk_state == GK_END_TXN:
                trk.gk_state = GK_IDLE
                trk.advance_txn_id()
                self._notify()
                self._log(f'  → {s}  (→ IDLE, next_id={trk.txn_id})')
            else:
                self._log(f'  → {s}')
            return gk_build(s)

        elif cmd == 'B':
            # Стоп/пауза
            if trk.gk_state == GK_FUELLING:
                trk.stop_dispensing()
                self._notify()
            s = trk.state_str()
            self._log(f'  → {s}')
            return gk_build(s)

        elif cmd == 'G':
            # Возобновить
            if trk.gk_state == GK_STOPPED:
                trk.gk_state = GK_STARTED
                trk.start_dispensing()
                self._notify()
            s = trk.state_str()
            self._log(f'  → {s}')
            return gk_build(s)

        elif cmd == 'W':
            # Запись параметра Wnnxxxx → Znnxxxx
            param_s = payload[1:].decode('ascii', errors='replace')
            s = f'Z{param_s}'
            self._log(f'  → {s}')
            return gk_build(s)

        elif cmd == 'Z':
            # Чтение параметра Znn → Znn0000
            nn = payload[1:3].decode('ascii', errors='replace')
            s = f'Z{nn}0000'
            self._log(f'  → {s}')
            return gk_build(s)

        elif cmd == 'D':
            # Переключение канала — эхо
            s = payload.decode('ascii', errors='replace')
            self._log(f'  → {s} (echo)')
            return gk_build(s)

        else:
            self._log(f'  [GK UNKNOWN] {cmd}')
            return None


# ═══════════════════════════════════════════════════════════════════════════════
#  ФОНОВЫЙ ПОТОК (последовательный порт)
# ═══════════════════════════════════════════════════════════════════════════════

class SerialWorker(threading.Thread):
    def __init__(self, port: str, protocol: str, processor, log_cb=None):
        super().__init__(daemon=True)
        self.port      = port
        self.protocol  = protocol   # 'AZT' или 'GasKit'
        self.processor = processor
        self._log_cb   = log_cb
        self._stop_evt = threading.Event()
        self.error     = None

    def run(self):
        try:
            if self.protocol == 'AZT':
                ser = serial.Serial(
                    port=self.port, baudrate=4800,
                    bytesize=serial.SEVENBITS, parity=serial.PARITY_EVEN,
                    stopbits=serial.STOPBITS_TWO, timeout=0.1)
            else:
                ser = serial.Serial(
                    port=self.port, baudrate=9600,
                    bytesize=serial.EIGHTBITS, parity=serial.PARITY_NONE,
                    stopbits=serial.STOPBITS_ONE, timeout=0.1)
        except Exception as e:
            self.error = str(e); return

        buf = bytearray()
        while not self._stop_evt.is_set():
            try:
                chunk = ser.read(64)
            except Exception as e:
                self.error = str(e); break
            if chunk:
                buf.extend(chunk)
            while True:
                resp = self.processor.feed(buf)
                if resp is None: break
                if resp:
                    time.sleep(0.005)
                    try:
                        ser.write(resp)
                        if self._log_cb:
                            self._log_cb(f'TX  {resp.hex(" ").upper()}')
                    except Exception as e:
                        self.error = str(e); break

        if ser.is_open:
            ser.close()

    def stop(self):
        self._stop_evt.set()


# ═══════════════════════════════════════════════════════════════════════════════
#  ЦВЕТА И СТИЛИ
# ═══════════════════════════════════════════════════════════════════════════════

CLR_BG      = '#1e2228'
CLR_PANEL   = '#252930'
CLR_DISPLAY = '#0d1117'
CLR_GREEN   = '#00e676'
CLR_AMBER   = '#ffab00'
CLR_RED     = '#ff5252'
CLR_BLUE    = '#448aff'
CLR_GRAY    = '#78909c'
CLR_WHITE   = '#eceff1'
CLR_BORDER  = '#37474f'
CLR_PURPLE  = '#bb86fc'

AZT_STATUS_STYLE = {
    ST_OFF_RK_IN:  ('Выключена  Кран: в кронштейне',     CLR_GRAY),
    ST_OFF_RK_OUT: ('Выключена  Кран: поднят',            CLR_AMBER),
    ST_AUTHORIZED: ('Санкционировано  Ожидание крана',    CLR_BLUE),
    ST_DISPENSING: ('ОТПУСК ТОПЛИВА',                     CLR_GREEN),
    ST_DONE:       ('Отпуск завершён  Ожидание подтв.',   CLR_AMBER),
    ST_BMU_DOSE:   ('Задана доза с БМУ',                  CLR_PURPLE),
}

GK_STATUS_STYLE = {
    GK_IDLE:          ('Ожидание',                            CLR_GRAY),
    GK_CALLING:       ('Пистолет поднят (без авторизации)',   CLR_AMBER),
    GK_AUTHORIZED:    ('Авторизовано  Ожидание пистолета',    CLR_BLUE),
    GK_STARTED:       ('Запуск...',                           CLR_BLUE),
    GK_SUSP_STARTED:  ('Заморожен (запуск)',                  CLR_AMBER),
    GK_FUELLING:      ('ОТПУСК ТОПЛИВА',                      CLR_GREEN),
    GK_SUSP_FUELLING: ('Приостановлен',                       CLR_AMBER),
    GK_STOPPED:       ('Отпуск завершён',                     CLR_AMBER),
    GK_END_TXN:       ('Конец транзакции  Ожидание N',        CLR_AMBER),
}


# ═══════════════════════════════════════════════════════════════════════════════
#  ГЛАВНОЕ ОКНО
# ═══════════════════════════════════════════════════════════════════════════════

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title('Эмулятор ТРК — АЗТ v2.0 / GasKitLink v1.2')
        self.geometry('940x700')
        self.minsize(860, 660)
        self.configure(bg=CLR_BG)
        try: self.iconbitmap(default='')
        except Exception: pass

        self._azt_state = AZTState(net_addr=1)
        self._gk_state  = GasKitState()
        self._azt_state.on_done = self._on_dispense_done
        self._gk_state.on_done  = self._on_dispense_done

        self.worker    = None
        self.processor = None
        self._log_q    = queue.Queue()
        self._state_q  = queue.Queue()

        self._build_ui()
        self._refresh_ports()
        self._poll()

    # ── Свойства ─────────────────────────────────────────────────────────────

    @property
    def _is_gaskit(self) -> bool:
        return self._proto_var.get() == 'GasKitLink v1.2'

    @property
    def _trk(self):
        return self._gk_state if self._is_gaskit else self._azt_state

    # ── Построение интерфейса ────────────────────────────────────────────────

    def _build_ui(self):
        # ── Верхняя панель ────────────────────────────────────────────────────
        top = tk.Frame(self, bg=CLR_PANEL, pady=8, padx=10)
        top.pack(fill=tk.X, side=tk.TOP)

        # Протокол
        tk.Label(top, text='Протокол:', bg=CLR_PANEL, fg=CLR_WHITE,
                 font=('Segoe UI', 10)).pack(side=tk.LEFT)
        self._proto_var = tk.StringVar(value='АЗТ v2.0')
        self._proto_cb  = ttk.Combobox(top, textvariable=self._proto_var,
                                        width=16, state='readonly',
                                        values=['АЗТ v2.0', 'GasKitLink v1.2'],
                                        font=('Segoe UI', 10))
        self._proto_cb.pack(side=tk.LEFT, padx=(4, 16))
        self._proto_cb.bind('<<ComboboxSelected>>', self._on_proto_change)

        # Порт
        tk.Label(top, text='Порт:', bg=CLR_PANEL, fg=CLR_WHITE,
                 font=('Segoe UI', 10)).pack(side=tk.LEFT)
        self._port_var = tk.StringVar()
        self._port_cb  = ttk.Combobox(top, textvariable=self._port_var,
                                       width=10, state='readonly',
                                       font=('Segoe UI', 10))
        self._port_cb.pack(side=tk.LEFT, padx=(4, 4))
        tk.Button(top, text='⟳', command=self._refresh_ports,
                  bg=CLR_PANEL, fg=CLR_WHITE, relief=tk.FLAT,
                  font=('Segoe UI', 11), cursor='hand2',
                  activebackground=CLR_BORDER).pack(side=tk.LEFT, padx=(0, 12))

        # Адрес (только для АЗТ)
        self._addr_frame = tk.Frame(top, bg=CLR_PANEL)
        self._addr_frame.pack(side=tk.LEFT)
        tk.Label(self._addr_frame, text='Адрес ТРК:', bg=CLR_PANEL,
                 fg=CLR_WHITE, font=('Segoe UI', 10)).pack(side=tk.LEFT)
        self._addr_var = tk.IntVar(value=1)
        tk.Spinbox(self._addr_frame, from_=1, to=255, textvariable=self._addr_var,
                   width=5, font=('Segoe UI', 10)).pack(side=tk.LEFT, padx=(4, 12))

        self._connect_btn = tk.Button(
            top, text='  Подключить  ', command=self._toggle_connect,
            bg='#1a6b2a', fg='white', activebackground='#22883a',
            font=('Segoe UI', 10, 'bold'), relief=tk.FLAT,
            padx=6, pady=4, cursor='hand2')
        self._connect_btn.pack(side=tk.LEFT, padx=(0, 16))

        self._conn_label = tk.Label(top, text='● Отключено',
                                    bg=CLR_PANEL, fg=CLR_RED,
                                    font=('Segoe UI', 10))
        self._conn_label.pack(side=tk.LEFT)

        # Индикатор протокола (скорость)
        self._baud_label = tk.Label(top, text='4800/7E2',
                                    bg=CLR_PANEL, fg=CLR_GRAY,
                                    font=('Consolas', 9))
        self._baud_label.pack(side=tk.RIGHT, padx=(0, 8))

        # ── Основная область ──────────────────────────────────────────────────
        main = tk.Frame(self, bg=CLR_BG)
        main.pack(fill=tk.BOTH, expand=True, padx=10, pady=6)

        left = tk.Frame(main, bg=CLR_BG)
        left.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self._build_display(left)

        right = tk.Frame(main, bg=CLR_BG, width=240)
        right.pack(side=tk.RIGHT, fill=tk.Y, padx=(10, 0))
        right.pack_propagate(False)
        self._build_controls(right)

        self._build_log()

    # ── Дисплей ───────────────────────────────────────────────────────────────

    def _build_display(self, parent):
        tk.Label(parent, text='ДИСПЛЕЙ  ТРК', bg=CLR_BG, fg=CLR_GRAY,
                 font=('Segoe UI', 9, 'bold')).pack(anchor=tk.W)

        disp = tk.Frame(parent, bg=CLR_DISPLAY,
                        highlightbackground=CLR_BORDER, highlightthickness=1)
        disp.pack(fill=tk.BOTH, expand=True)

        pad = dict(padx=16)

        sf = tk.Frame(disp, bg=CLR_DISPLAY)
        sf.pack(fill=tk.X, pady=(14, 4), **pad)
        tk.Label(sf, text='СТАТУС', bg=CLR_DISPLAY, fg=CLR_GRAY,
                 font=('Consolas', 9)).pack(anchor=tk.W)
        self._status_lbl = tk.Label(sf, text='Выключена  Кран: в кронштейне',
                                    bg=CLR_DISPLAY, fg=CLR_GRAY,
                                    font=('Segoe UI', 13, 'bold'))
        self._status_lbl.pack(anchor=tk.W)

        tk.Frame(disp, bg=CLR_BORDER, height=1).pack(fill=tk.X, **pad)

        for label, attr, color, init in [
            ('ЛИТРЫ  (текущие)', 'cur_lbl',  CLR_GREEN, '000.00'),
            ('СУММА  (руб.)',    'rub_lbl',  CLR_AMBER, '0000.00'),
        ]:
            f = tk.Frame(disp, bg=CLR_DISPLAY)
            f.pack(fill=tk.X, pady=(8, 0), **pad)
            tk.Label(f, text=label, bg=CLR_DISPLAY, fg=CLR_GRAY,
                     font=('Consolas', 9)).pack(anchor=tk.W)
            lbl = tk.Label(f, text=init, bg=CLR_DISPLAY, fg=color,
                           font=('Consolas', 28, 'bold'))
            lbl.pack(anchor=tk.W)
            setattr(self, attr, lbl)

        tk.Frame(disp, bg=CLR_BORDER, height=1).pack(fill=tk.X, pady=6, **pad)

        fields = tk.Frame(disp, bg=CLR_DISPLAY)
        fields.pack(fill=tk.X, **pad, pady=(0, 10))
        fields.columnconfigure(1, weight=1)
        fields.columnconfigure(3, weight=1)

        for i, (caption, attr) in enumerate([
            ('Цена ₽/л', 'price_lbl'), ('Доза',      'dose_lbl'),
            ('Транзакция','txn_lbl'),  ('Адрес/ID',   'addr_lbl'),
        ]):
            row, col = divmod(i, 2)
            cb = col * 2
            tk.Label(fields, text=caption + ':', bg=CLR_DISPLAY,
                     fg=CLR_GRAY, font=('Consolas', 9)
                     ).grid(row=row, column=cb, sticky=tk.W, pady=3, padx=(0, 4))
            lbl = tk.Label(fields, text='—', bg=CLR_DISPLAY,
                           fg=CLR_WHITE, font=('Consolas', 11, 'bold'))
            lbl.grid(row=row, column=cb+1, sticky=tk.W, pady=3, padx=(0, 20))
            setattr(self, attr, lbl)

    # ── Кнопки управления ────────────────────────────────────────────────────

    def _build_controls(self, parent):
        tk.Label(parent, text='УПРАВЛЕНИЕ', bg=CLR_BG, fg=CLR_GRAY,
                 font=('Segoe UI', 9, 'bold')).pack(anchor=tk.W)

        btn_frame = tk.Frame(parent, bg=CLR_BG)
        btn_frame.pack(fill=tk.X, pady=(4, 0))

        self._lift_btn = tk.Button(
            btn_frame, text='⬆  ПОДНЯТЬ ПИСТОЛЕТ',
            command=self._lift_nozzle,
            bg='#1a5c2a', fg='white', activebackground='#22803a',
            font=('Segoe UI', 12, 'bold'), relief=tk.FLAT,
            padx=10, pady=16, cursor='hand2', width=20,
            disabledforeground='#4a4a4a')
        self._lift_btn.pack(fill=tk.X, pady=(6, 4))

        self._hang_btn = tk.Button(
            btn_frame, text='⬇  ПОВЕСИТЬ ПИСТОЛЕТ',
            command=self._hang_nozzle,
            bg='#5c1a1a', fg='white', activebackground='#7a2222',
            font=('Segoe UI', 12, 'bold'), relief=tk.FLAT,
            padx=10, pady=16, cursor='hand2', width=20,
            disabledforeground='#4a4a4a')
        self._hang_btn.pack(fill=tk.X, pady=4)

        tk.Frame(parent, bg=CLR_BORDER, height=1).pack(fill=tk.X, pady=8)

        tk.Label(parent, text='АВТОНОМНЫЙ РЕЖИМ', bg=CLR_BG, fg=CLR_GRAY,
                 font=('Segoe UI', 9, 'bold')).pack(anchor=tk.W)

        auto_frame = tk.Frame(parent, bg=CLR_BG)
        auto_frame.pack(fill=tk.X, pady=(4, 0))

        row1 = tk.Frame(auto_frame, bg=CLR_BG)
        row1.pack(fill=tk.X, pady=2)
        tk.Label(row1, text='Цена ₽/л:', bg=CLR_BG, fg=CLR_WHITE,
                 font=('Segoe UI', 10), width=9, anchor=tk.W).pack(side=tk.LEFT)
        self._auto_price_var = tk.StringVar(value='52.50')
        tk.Entry(row1, textvariable=self._auto_price_var, width=8,
                 font=('Consolas', 11), bg='#2d3340', fg=CLR_WHITE,
                 insertbackground=CLR_WHITE, relief=tk.FLAT).pack(side=tk.LEFT)

        row2 = tk.Frame(auto_frame, bg=CLR_BG)
        row2.pack(fill=tk.X, pady=2)
        tk.Label(row2, text='Доза (л):', bg=CLR_BG, fg=CLR_WHITE,
                 font=('Segoe UI', 10), width=9, anchor=tk.W).pack(side=tk.LEFT)
        self._auto_dose_var = tk.StringVar(value='20.00')
        tk.Entry(row2, textvariable=self._auto_dose_var, width=8,
                 font=('Consolas', 11), bg='#2d3340', fg=CLR_WHITE,
                 insertbackground=CLR_WHITE, relief=tk.FLAT).pack(side=tk.LEFT)

        self._start_btn = tk.Button(
            parent, text='▶  СТАРТ', command=self._start_dispensing,
            bg='#1a4a6b', fg='white', activebackground='#226090',
            font=('Segoe UI', 12, 'bold'), relief=tk.FLAT,
            padx=10, pady=12, cursor='hand2', width=20,
            disabledforeground='#4a4a4a')
        self._start_btn.pack(fill=tk.X, pady=(6, 4))

        self._stop_btn = tk.Button(
            parent, text='■  СТОП', command=self._stop_dispensing,
            bg='#6b4a1a', fg='white', activebackground='#906022',
            font=('Segoe UI', 12, 'bold'), relief=tk.FLAT,
            padx=10, pady=12, cursor='hand2', width=20,
            disabledforeground='#4a4a4a')
        self._stop_btn.pack(fill=tk.X, pady=4)

        tk.Frame(parent, bg=CLR_BORDER, height=1).pack(fill=tk.X, pady=8)

        tk.Label(parent, text='Суммарник:', bg=CLR_BG,
                 fg=CLR_GRAY, font=('Segoe UI', 9, 'bold')).pack(anchor=tk.W)
        self._tot_lbl = tk.Label(parent, text='Литры: 0.00',
                                 bg=CLR_BG, fg=CLR_GRAY,
                                 font=('Consolas', 10), justify=tk.LEFT)
        self._tot_lbl.pack(anchor=tk.W, pady=(2, 0))

    # ── Лог ──────────────────────────────────────────────────────────────────

    def _build_log(self):
        log_frame = tk.Frame(self, bg=CLR_BG)
        log_frame.pack(fill=tk.X, side=tk.BOTTOM, padx=10, pady=(0, 6))
        tk.Label(log_frame, text='ЛОГ ОБМЕНА', bg=CLR_BG, fg=CLR_GRAY,
                 font=('Segoe UI', 9, 'bold')).pack(anchor=tk.W)
        self._log_txt = tk.Text(
            log_frame, height=8, bg=CLR_DISPLAY, fg='#aaaaaa',
            font=('Consolas', 9), relief=tk.FLAT, state=tk.DISABLED,
            wrap=tk.NONE, highlightbackground=CLR_BORDER, highlightthickness=1)
        self._log_txt.pack(fill=tk.X)
        self._log_txt.tag_config('rx',   foreground='#80cbc4')
        self._log_txt.tag_config('tx',   foreground='#ffcc80')
        self._log_txt.tag_config('info', foreground='#b0bec5')
        self._log_txt.tag_config('err',  foreground='#ef9a9a')

    # ──────────────────────────────────────────────────────────────────────────
    #  Опрос очередей / обновление GUI
    # ──────────────────────────────────────────────────────────────────────────

    def _poll(self):
        while not self._log_q.empty():
            self._append_log(self._log_q.get_nowait())
        while not self._state_q.empty():
            self._state_q.get_nowait()

        self._update_display()

        if self.worker and self.worker.error:
            err = self.worker.error; self.worker.error = None
            self._append_log(f'ОШИБКА ПОРТА: {err}', 'err')
            self._do_disconnect()

        self.after(200, self._poll)

    def _update_display(self):
        if self._is_gaskit:
            self._update_display_gk()
        else:
            self._update_display_azt()
        self._update_buttons()

    def _update_display_azt(self):
        trk = self._azt_state
        st_text, st_color = AZT_STATUS_STYLE.get(trk.status, ('?', CLR_GRAY))
        self._status_lbl.config(text=st_text, fg=st_color)
        with trk._lock:
            cur       = trk.cur_liters
            full_rub  = trk.full_rubles
            total_lit = trk.total_liters
            price     = trk.price_kop / 100.0
            preset    = trk.preset_lit
            txn       = trk.transaction
            addr      = trk.net_addr
        self.cur_lbl.config(text=f'{cur:>7.2f}')
        self.rub_lbl.config(text=f'{full_rub:>8.2f}')
        self.price_lbl.config(text=f'{price:.2f}')
        self.dose_lbl.config(text=f'{preset:.2f} л')
        self.txn_lbl.config(text=str(txn))
        self.addr_lbl.config(text=str(addr))
        self._tot_lbl.config(text=f'Литры: {total_lit:,.2f}')

    def _update_display_gk(self):
        trk = self._gk_state
        st_text, st_color = GK_STATUS_STYLE.get(trk.gk_state, ('?', CLR_GRAY))
        self._status_lbl.config(text=st_text, fg=st_color)
        with trk._lock:
            cur_l   = trk.cur_cl / 100.0
            cur_r   = trk.cur_kop / 100.0
            total_l = trk.total_cl / 100.0
            price   = trk.price_kop / 100.0
            preset  = trk.preset_cl / 100.0
        self.cur_lbl.config(text=f'{cur_l:>7.2f}')
        self.rub_lbl.config(text=f'{cur_r:>8.2f}')
        self.price_lbl.config(text=f'{price:.2f}')
        self.dose_lbl.config(text=f'{preset:.2f} л')
        self.txn_lbl.config(text=trk.txn_id)
        self.addr_lbl.config(text='00/01')
        self._tot_lbl.config(text=f'Литры: {total_l:,.2f}')

    def _update_buttons(self):
        if self._is_gaskit:
            self._update_buttons_gk()
        else:
            self._update_buttons_azt()

    def _update_buttons_azt(self):
        trk = self._azt_state
        connected = self.worker and self.worker.is_alive()

        lift_ok = (trk.status == ST_OFF_RK_IN)
        self._lift_btn.config(
            state=tk.NORMAL if lift_ok else tk.DISABLED,
            bg='#1a5c2a' if lift_ok else '#2a2a2a')

        hang_ok = trk.status in (ST_OFF_RK_OUT, ST_AUTHORIZED, ST_DISPENSING, ST_DONE)
        self._hang_btn.config(
            state=tk.NORMAL if hang_ok else tk.DISABLED,
            bg='#5c1a1a' if hang_ok else '#2a2a2a')

        if trk.status == ST_AUTHORIZED:
            start_ok = True
        elif not connected and trk.status in (ST_OFF_RK_IN, ST_OFF_RK_OUT):
            start_ok = True
        else:
            start_ok = False
        self._start_btn.config(
            state=tk.NORMAL if start_ok else tk.DISABLED,
            bg='#1a4a6b' if start_ok else '#2a2a2a')

        stop_ok = (trk.status == ST_DISPENSING)
        self._stop_btn.config(
            state=tk.NORMAL if stop_ok else tk.DISABLED,
            bg='#6b4a1a' if stop_ok else '#2a2a2a')

    def _update_buttons_gk(self):
        trk = self._gk_state
        connected = self.worker and self.worker.is_alive()

        # ПОДНЯТЬ: из IDLE (calling) или из AUTHORIZED (начать отпуск)
        lift_ok = trk.gk_state in (GK_IDLE, GK_AUTHORIZED)
        self._lift_btn.config(
            state=tk.NORMAL if lift_ok else tk.DISABLED,
            bg='#1a5c2a' if lift_ok else '#2a2a2a')

        # ПОВЕСИТЬ: пистолет поднят (state 2,4,5,6,7,8)
        hang_ok = trk.gk_state in (GK_CALLING, GK_STARTED, GK_SUSP_STARTED,
                                    GK_FUELLING, GK_SUSP_FUELLING, GK_STOPPED)
        self._hang_btn.config(
            state=tk.NORMAL if hang_ok else tk.DISABLED,
            bg='#5c1a1a' if hang_ok else '#2a2a2a')

        # СТАРТ: AUTHORIZED (от АСУ) или автономно в IDLE (порт закрыт)
        if trk.gk_state == GK_AUTHORIZED:
            start_ok = True
        elif not connected and trk.gk_state == GK_IDLE:
            start_ok = True
        else:
            start_ok = False
        self._start_btn.config(
            state=tk.NORMAL if start_ok else tk.DISABLED,
            bg='#1a4a6b' if start_ok else '#2a2a2a')

        # СТОП: во время отпуска
        stop_ok = trk.gk_state in (GK_FUELLING, GK_STARTED)
        self._stop_btn.config(
            state=tk.NORMAL if stop_ok else tk.DISABLED,
            bg='#6b4a1a' if stop_ok else '#2a2a2a')

    # ──────────────────────────────────────────────────────────────────────────
    #  Лог
    # ──────────────────────────────────────────────────────────────────────────

    def _append_log(self, msg: str, tag: str = None):
        ts = time.strftime('%H:%M:%S')
        line = f'{ts}  {msg}\n'
        if tag is None:
            tag = ('rx' if msg.startswith('RX') else
                   'tx' if msg.startswith('TX') else 'info')
        self._log_txt.config(state=tk.NORMAL)
        self._log_txt.insert(tk.END, line, tag)
        self._log_txt.see(tk.END)
        self._log_txt.config(state=tk.DISABLED)
        lines = int(self._log_txt.index('end-1c').split('.')[0])
        if lines > 500:
            self._log_txt.config(state=tk.NORMAL)
            self._log_txt.delete('1.0', '100.0')
            self._log_txt.config(state=tk.DISABLED)

    def _log_cb(self, msg: str):
        self._log_q.put(msg)

    def _state_cb(self):
        self._state_q.put(1)

    # ──────────────────────────────────────────────────────────────────────────
    #  Подключение / отключение
    # ──────────────────────────────────────────────────────────────────────────

    def _on_proto_change(self, event=None):
        if self.worker and self.worker.is_alive():
            return  # нельзя менять протокол пока порт открыт
        if self._is_gaskit:
            self._baud_label.config(text='9600/8N1')
            self._addr_frame.pack_forget()
        else:
            self._baud_label.config(text='4800/7E2')
            self._addr_frame.pack(side=tk.LEFT)
        self._append_log(f'[ПРОТОКОЛ] {self._proto_var.get()}', 'info')

    def _refresh_ports(self):
        if not HAS_SERIAL:
            self._port_cb['values'] = ['(pyserial не установлен)']; return
        ports = [p.device for p in serial.tools.list_ports.comports()]
        if not ports: ports = ['(нет портов)']
        self._port_cb['values'] = ports
        if self._port_var.get() not in ports: self._port_cb.current(0)

    def _toggle_connect(self):
        if self.worker and self.worker.is_alive():
            self._do_disconnect()
        else:
            self._do_connect()

    def _do_connect(self):
        if not HAS_SERIAL:
            messagebox.showerror('Ошибка',
                'pyserial не установлен.\nВыполните: pip install pyserial'); return
        port = self._port_var.get()
        if not port or port.startswith('('):
            messagebox.showwarning('Внимание', 'Выберите COM-порт из списка.'); return

        if self._is_gaskit:
            self.processor = GasKitPacketProcessor(
                self._gk_state, log_cb=self._log_cb, state_cb=self._state_cb)
            proto_key = 'GasKit'
        else:
            self._azt_state.net_addr = self._addr_var.get()
            self.processor = AZTPacketProcessor(
                self._azt_state, log_cb=self._log_cb, state_cb=self._state_cb)
            proto_key = 'AZT'

        self.worker = SerialWorker(
            port=port, protocol=proto_key,
            processor=self.processor, log_cb=self._log_cb)
        self.worker.start()
        self.after(400, self._check_connect)

    def _check_connect(self):
        if self.worker and self.worker.error:
            err = self.worker.error; self.worker = None
            messagebox.showerror('Ошибка подключения',
                f'Не удалось открыть порт:\n{err}'); return
        port = self._port_var.get()
        proto = self._proto_var.get()
        self._conn_label.config(text=f'● {port}  подключён', fg=CLR_GREEN)
        self._connect_btn.config(text='  Отключить  ', bg='#6b1a1a')
        self._port_cb.config(state=tk.DISABLED)
        self._proto_cb.config(state=tk.DISABLED)
        baud = '9600/8N1' if self._is_gaskit else '4800/7E2'
        addr_info = '' if self._is_gaskit else f', адрес={self._azt_state.net_addr}'
        self._append_log(f'Открыт порт {port}  [{proto}  {baud}{addr_info}]', 'info')

    def _do_disconnect(self):
        if self.worker:
            self.worker.stop(); self.worker = None
        self._conn_label.config(text='● Отключено', fg=CLR_RED)
        self._connect_btn.config(text='  Подключить  ', bg='#1a6b2a')
        self._port_cb.config(state='readonly')
        self._proto_cb.config(state='readonly')
        self._append_log('Порт закрыт.', 'info')

    # ──────────────────────────────────────────────────────────────────────────
    #  Кнопки управления ТРК
    # ──────────────────────────────────────────────────────────────────────────

    def _lift_nozzle(self):
        if self._is_gaskit:
            self._lift_nozzle_gk()
        else:
            self._lift_nozzle_azt()

    def _lift_nozzle_azt(self):
        trk = self._azt_state
        if trk.status == ST_OFF_RK_IN:
            trk.rk_in = False; trk.status = ST_OFF_RK_OUT
            self._log_cb('[КНОПКА] Пистолет поднят  >>  OFF_RK_OUT(1)')

    def _lift_nozzle_gk(self):
        trk = self._gk_state
        if trk.gk_state == GK_IDLE:
            trk.gk_state = GK_CALLING
            self._log_cb('[КНОПКА] Пистолет поднят  >>  CALLING(2)')
        elif trk.gk_state == GK_AUTHORIZED:
            trk.gk_state = GK_STARTED
            trk.start_dispensing()
            self._log_cb('[КНОПКА] Пистолет поднят  >>  STARTED(4) → FUELLING(6)')

    def _hang_nozzle(self):
        if self._is_gaskit:
            self._hang_nozzle_gk()
        else:
            self._hang_nozzle_azt()

    def _hang_nozzle_azt(self):
        trk = self._azt_state
        if trk.status == ST_OFF_RK_OUT:
            trk.rk_in = True; trk.status = ST_OFF_RK_IN
            self._log_cb('[КНОПКА] Пистолет повешен  >>  OFF_RK_IN(0)')
        elif trk.status == ST_AUTHORIZED:
            trk.rk_in = True; trk.status = ST_OFF_RK_IN
            self._log_cb('[КНОПКА] Пистолет повешен  >>  OFF_RK_IN(0) (сброс авт.)')
        elif trk.status == ST_DISPENSING:
            trk.stop_dispensing(); trk.rk_in = True
            self._log_cb('[КНОПКА] Пистолет повешен  >>  DONE(4) ОТПУСК ОСТАНОВЛЕН')
        elif trk.status == ST_DONE:
            trk.rk_in = True; trk.status = ST_OFF_RK_IN
            self._log_cb('[КНОПКА] Пистолет повешен  >>  OFF_RK_IN(0)')

    def _hang_nozzle_gk(self):
        trk = self._gk_state
        if trk.gk_state == GK_CALLING:
            trk.gk_state = GK_IDLE
            self._log_cb('[КНОПКА] Пистолет повешен  >>  IDLE(1)')
        elif trk.gk_state in (GK_STARTED, GK_FUELLING, GK_SUSP_FUELLING):
            trk.stop_dispensing()
            self._log_cb('[КНОПКА] Пистолет повешен  >>  STOPPED(8) ОТПУСК ОСТАНОВЛЕН')
        elif trk.gk_state == GK_STOPPED:
            trk.gk_state = GK_END_TXN
            self._log_cb('[КНОПКА] Пистолет повешен  >>  END_TXN(9)')

    def _start_dispensing(self):
        if self._is_gaskit:
            self._start_dispensing_gk()
        else:
            self._start_dispensing_azt()

    def _start_dispensing_azt(self):
        trk = self._azt_state
        connected = self.worker and self.worker.is_alive()
        if not connected and trk.status in (ST_OFF_RK_IN, ST_OFF_RK_OUT):
            try:
                price = float(self._auto_price_var.get().replace(',', '.'))
                dose  = float(self._auto_dose_var.get().replace(',', '.'))
                if price <= 0 or dose <= 0: raise ValueError
            except ValueError:
                messagebox.showwarning('Ввод', 'Укажите цену > 0 и дозу > 0.'); return
            trk.price_kop = int(round(price * 100))
            trk.preset_lit = dose; trk.preset_mode = 'L'
            trk.preset_rub = dose * price
            trk.full_liters = 0.0; trk.full_rubles = 0.0; trk.cur_liters = 0.0
            trk.transaction += 1; trk.rk_in = False; trk.status = ST_DISPENSING
            trk.start_dispensing()
            self._append_log(f'[АВТО] Цена={price:.2f} Доза={dose:.2f}л  >>  DISPENSING', 'info')
            return
        if trk.status == ST_AUTHORIZED:
            trk.rk_in = False; trk.status = ST_DISPENSING
            trk.start_dispensing()
            self._log_cb('[КНОПКА] СТАРТ  >>  DISPENSING(3)')

    def _start_dispensing_gk(self):
        trk = self._gk_state
        connected = self.worker and self.worker.is_alive()
        if not connected and trk.gk_state == GK_IDLE:
            try:
                price = float(self._auto_price_var.get().replace(',', '.'))
                dose  = float(self._auto_dose_var.get().replace(',', '.'))
                if price <= 0 or dose <= 0: raise ValueError
            except ValueError:
                messagebox.showwarning('Ввод', 'Укажите цену > 0 и дозу > 0.'); return
            trk.price_kop   = int(round(price * 100))
            trk.preset_cl   = int(round(dose * 100))
            trk.preset_mode = 'V'
            trk.cur_cl      = 0.0; trk.cur_kop = 0.0
            trk.gk_state    = GK_STARTED
            trk.start_dispensing()
            self._append_log(f'[АВТО GK] Цена={price:.2f} Доза={dose:.2f}л  >>  FUELLING', 'info')
            return
        if trk.gk_state == GK_AUTHORIZED:
            trk.gk_state = GK_STARTED
            trk.start_dispensing()
            self._log_cb('[КНОПКА] СТАРТ  >>  STARTED(4) → FUELLING(6)')

    def _stop_dispensing(self):
        if self._is_gaskit:
            trk = self._gk_state
            if trk.gk_state in (GK_FUELLING, GK_STARTED):
                trk.stop_dispensing()
                self._log_cb('[КНОПКА] СТОП  >>  STOPPED(8)')
        else:
            trk = self._azt_state
            if trk.status == ST_DISPENSING:
                trk.stop_dispensing()
                self._log_cb('[КНОПКА] СТОП  >>  DONE(4)')

    # ──────────────────────────────────────────────────────────────────────────
    #  Callback завершения отпуска
    # ──────────────────────────────────────────────────────────────────────────

    def _on_dispense_done(self, reason: str):
        if reason == 'dose':
            self._log_q.put('[АВТО] Доза выдана — отпуск завершён')
        else:
            self._log_q.put('[АВТО] Отпуск остановлен')

    # ──────────────────────────────────────────────────────────────────────────
    #  Закрытие
    # ──────────────────────────────────────────────────────────────────────────

    def on_close(self):
        self._do_disconnect()
        self.destroy()


# ═══════════════════════════════════════════════════════════════════════════════
#  ЗАПУСК
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    if not HAS_SERIAL:
        root = tk.Tk(); root.withdraw()
        messagebox.showerror(
            'Зависимость не установлена',
            'Необходимо установить pyserial:\n\npip install pyserial\n\n'
            'Затем запустите программу снова.')
        root.destroy(); sys.exit(1)

    app = App()
    app.protocol('WM_DELETE_WINDOW', app.on_close)
    app.mainloop()


if __name__ == '__main__':
    main()
