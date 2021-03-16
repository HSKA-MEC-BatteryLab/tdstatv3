# TDstatv3
A USB-controlled potentiostat/galvanostat for thin-film battery characterization

## Introduction
This repository contains all the necessary design files to build your own USB-controlled potentiostat/galvanostat.
These files are intended as supplementary information accompanying the whitepaper at https://arxiv.org/pdf/1701.07650.pdf.

## Repository contents

### Directories
* `kicad`: KiCad design files (schematic diagram and PCB layout).
* `firmware`: Source code and compiled firmware for the PIC16F1459 microcontroller. Uses Microchip's XC8 compiler.
* `python`: Contains `tdstatv3.py`; run this file with Python 3 to bring up a GUI measurement tool.
* `gerber`: PCB design files in Gerber format, the universal standard for PCB manufacturing.
* `datasheets`: Datasheets in pdf format for the integrated circuits used in this design.
* `drivers`: Libusb drivers for Windows (not necessary on other operating systems).

### Files
* `full_schematic.pdf`: Complete schematic diagram in pdf format.
* `parts_list.txt`: Complete parts list, useful when ordering components.
* `pcb_3dview.png`: 3D renders of the PCB design, useful for verification of the PCB layout.
* `pcb_fabrication_diagram.pdf`: Front side of PCB with component locations and values, useful for circuit assembly.
* `photograph.jpg`: A photograph of the assembled circuit, using a PCB manufactured by [OSH Park](https://oshpark.com/).
* `LICENSE`: a copy of the GNU GPLv3 license.
* `README.md`: This file.

## USB access on Linux
In order to access the device without requiring root privileges, create a file
`/etc/udev/rules.d/99-tdstatv3.rules` containing the line

```
SUBSYSTEM=="usb", ATTRS{idVendor}=="a0a0", ATTRS{idProduct}=="0002", GROUP="plugdev", MODE="0666"
```
This assumes that the current user is a member of the `plugdev` group, and that the default USB Vendor and Product ID's
as coded in the microcontroller firmware are used; if not, these values need to be adjusted.

## USB access on Windows
The USB Potentiostat uses the Libusb generic usb driver to connect the device to the Python program. Due to Window's 10's security, signed drivers are necessary, creating many problems for end-users. There are ways to use a generic Libusb driver by disabling security on your Windows PC during the installation process. You can find guides on how to accomplish that installation online.

Alternately, good results have been obtained by using the program Zadig (version 2.5) available here: https://zadig.akeo.ie/ From the drop down device list, select the USB Potentiostat/Galvanostat, it may be neccesary to select "List all devices" on the options menu. In the driver window, select the preferred driver, LibUSB-win32 or WinUSB and click "install driver". You can check to see if the driver installed correctly by looking for the Potentiostat under USB Devices in your computer's Device Manager. If the device is not found, uninstall the driver for the USB-Potentiostat in the Device Manager and use Zadig to try the other driver. DO NOT SIMPLY "REPLACE" THE INCORRECT DRIVER, UNINSTALL IT! Windows will remember the incorrect driver and default to it every time the device is re-plugged.

## Credits
* Thomas Dobbelaere
* email: thomas.dobbelaere@gmail.com

## License
The contents of this repository are licensed under the GNU General Public License (GPL).
