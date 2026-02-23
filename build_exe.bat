@echo off
chcp 65001 >nul
echo ========================================
echo  Сборка AZT TRK Emulator в EXE
echo ========================================

echo Устанавливаю зависимости...
pip install pyserial pyinstaller --quiet

echo Собираю EXE...
pyinstaller ^
  --onefile ^
  --windowed ^
  --name "AZT_TRK_Emulator" ^
  --add-data "." ^
  azt_emulator_gui.py

if exist dist\AZT_TRK_Emulator.exe (
    echo.
    echo ========================================
    echo  ГОТОВО! Файл: dist\AZT_TRK_Emulator.exe
    echo ========================================
    copy dist\AZT_TRK_Emulator.exe . >nul
    echo Скопирован в текущую папку.
) else (
    echo.
    echo ОШИБКА: EXE не создан. Проверьте вывод выше.
)
pause
