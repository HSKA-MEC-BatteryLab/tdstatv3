#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# This Python program allows control over the USB potentiostat/galvanostat using a graphical user interface. It supports
# real-time data acquisition and plotting, manual control and calibration, and three pre-programmed measurement methods
# geared towards battery research (staircase cyclic voltammetry, constant-current charge/discharge, and rate testing).
# It is cross-platform, requiring only a working installation of Python 3.x together with the Numpy, Scipy, PyUSB, and
# PyQtGraph packages.

# Author: Thomas Dobbelaere
# License: GPL


import collections
import datetime
import logging
# import usb.core, usb.util
import os.path
import platform
import sys
import time
import timeit
#import json

# Depending on system, may be necessary to comment out pyqtgraph or the QtCore and QtGui modules from PyQt5
#from pyqtgraph.Qt import QtCore, QtGui

import PyQt5
import numpy
import pyqtgraph
import pyqtgraph.exporters
import scipy.integrate
import usb
from PyQt5 import QtWidgets, QtCore, QtGui
import json

# variable initializations
usb_debug_flag = False
usb_vid = "0xa0a0"  # Default USB vendor ID
usb_pid = "0x0002"  # Default USB product ID
current_range_list = ["20 mA", u"200 µA", u"2 µA"]
shunt_calibration = [1., 1.,
                     1.]  # Fine adjustment for shunt resistors, containing values of R1/10ohm, R2/1kohm, R3/100kohm
                        # (can also be adjusted in the GUI)
currentrange = 0  # Default current range (expressed as index in current_range_list)
units_list = ["Potential (V)", "Current (mA)", "DAC Code"]
dev = None  # Global object which is reserved for the USB device
usb_device_list = []  # Creates a list to hold all devices found in scan
current_offset = 0.  # Current offset in DAC counts
potential_offset = 0.  # Potential offset in DAC counts
potential = 0.  # Measured potential in V
current = 0.  # Measured current in mA
last_potential_values = collections.deque(maxlen=200)
last_current_values = collections.deque(maxlen=200)
raw_potential = 0  # Measured potential in ADC counts
raw_current = 0  # Measured current in ADC counts
last_raw_potential_values = collections.deque(maxlen=200)
last_raw_current_values = collections.deque(maxlen=200)
cv_parameters = {}  # Dictionary to hold the CV parameters
cv_duration = 0
test_start = None
test_end = None
cv_cycle = None
cd_parameters = {}  # Dictionary to hold the charge/discharge parameters
rate_parameters = {}  # Dictionary to hold the rate testing parameters
ocp_parameters = {}
temp_parameters = {}
overcounter, undercounter, skipcounter = 0, 0, 0  # Global counters used for automatic current ranging
time_of_last_adcread = 0.
adcread_interval = 0.09  # ADC sampling interval (in seconds)
logging_enabled = False  # Enable logging of potential and current in idle mode (can be adjusted in the GUI)
pen_color = ['y', 'r', 'g', 'c', 'm', 'w', "#663300", "#666699", "#ff9900", "#339933"]  # graph line color
cd_voltage_finish_flag = False
cd_in_finishing = False
cd_voltage_finish_mode = 0  # Possible Modes for voltage finish
cd_voltage_finish_time = {"start_time": 0, "end_time": 0, "semaphore": False}  # Start time of constant voltage,
                                                                            # semaphore flag for read/write operations
cd_voltage_finish_current = {"start_current": 0, "end_current": 0, "semaphore": False}  # Start current of constant
                                                                    # voltage, semaphore flag for read/write operations
control_mode = "POTENTIOSTATIC"
sequence_flag = False
seq_cv_ocv_flag = False
sequence_index = 0
test_sequence = {}
settling_counter = 5
temp_sensor_type = True  #True PT1000, False PT100

if platform.system() != "Windows":
    # On Linux/OSX, use the Qt timer
    busyloop_interval = 0
    qt_timer_period = 1e3 * adcread_interval  # convert to ms
else:
    # On MS Windows, system timing is inaccurate, so use a busy loop instead
    busyloop_interval = adcread_interval
    qt_timer_period = 0

# enables scaling for high resolution monitors, prevents window from being squished together
if hasattr(QtCore.Qt, 'AA_EnableHighDpiScaling'):
    PyQt5.QtWidgets.QApplication.setAttribute(QtCore.Qt.AA_EnableHighDpiScaling, True)


# related to scaling, but not found, functions without this
# if hasattr(QtCore, 'AA_UseHighDpiPixmaps'):
#	PyQt5.QtWidgets.QApplication.setAttribute(QtCore.Qt.AA_UseHighDpiPixmaps, True)


def GraphAutoExport(plot, filename):
    exporter = pyqtgraph.exporters.ImageExporter(plot.plotItem)
    base, ext = os.path.splitext(filename)
    exporter.export(base + '.png')


class StreamToLogger(object):
    """
    Fake file-like stream object that redirects writes to a logger instance.
    """

    def __init__(self, logger, log_level=logging.DEBUG):
        self.logger = logger
        self.log_level = log_level
        self.linebuf = ''

    def write(self, buf):
        for line in buf.rstrip().splitlines():
            self.logger.log(self.log_level, line.rstrip())

    def flush(self):
        pass


class AverageBuffer:
    """Collect samples and compute an average as soon as a sufficient number of samples is added."""

    def __init__(self, number_of_samples_to_average):
        self.number_of_samples_to_average = number_of_samples_to_average
        self.samples = []
        self.averagebuffer = []

    def add_sample(self, sample):
        self.samples.append(sample)
        if len(self.samples) >= self.number_of_samples_to_average:
            self.averagebuffer.append(sum(self.samples) / len(self.samples))
            self.samples = []

    def clear(self):
        self.samples = []
        self.averagebuffer = []


class States:
    """Expose a named list of states to be used as a simple state machine."""
    (
        NotConnected,
        Idle_Init,
        Idle,
        Sequence_Idle,
        Measuring_Offset,
        Stationary_Graph,
        Measuring_CV, Measuring_CD,
        Measuring_Rate,
        Measuring_OCP,
        Measuring_Temp
    ) = range(11)


state = States.NotConnected  # Initial state


def current_to_string(currentrange, current_in_mA):
    """Format the measured current into a string with appropriate units and number of significant digits."""
    abs_value = abs(current_in_mA)
    if currentrange == 0:
        if abs_value <= 9.9995:
            return u"%+6.3f mA" % current_in_mA
        else:
            return u"%+6.2f mA" % current_in_mA
    elif currentrange == 1:
        if abs_value < 9.9995e-2:
            return u"%+06.2f µA" % (current_in_mA * 1e3)
        else:
            return u"%+6.1f µA" % (current_in_mA * 1e3)
    elif currentrange == 2:
        return u"%+6.3f µA" % (current_in_mA * 1e3)


def potential_to_string(potential_in_V):
    """Format the measured potential into a string with appropriate units and number of significant digits."""
    return u"%+6.3f V" % potential_in_V


def twocomplement_to_decimal(msb, middlebyte, lsb):
    """Convert a 22-bit two-complement ADC value consisting of three bytes to a signed integer (see MCP3550 datasheet for details)."""
    ovh = (msb > 63) and (msb < 128)  # Check for overflow high (B22 set)
    ovl = (msb > 127)  # Check for overflow low (B23 set)
    combined_value = (msb % 64) * 2 ** 16 + middlebyte * 2 ** 8 + lsb  # Get rid of overflow bits
    if not ovh and not ovl:
        if msb > 31:  # B21 set -> negative number
            answer = combined_value - 2 ** 22
        else:
            answer = combined_value
    else:  # overflow
        if msb > 127:  # B23 set -> negative number
            answer = combined_value - 2 ** 22
        else:
            answer = combined_value
    return answer


def decimal_to_dac_bytes(value):
    """Convert a floating-point number, ranging from -2**19 to 2**19-1, to three data bytes in the proper format for the DAC1220."""
    code = 2 ** 19 + int(
        round(value))  # Convert the (signed) input value to an unsigned 20-bit integer with zero at midway
    code = numpy.clip(code, 0, 2 ** 20 - 1)  # If the input exceeds the boundaries of the 20-bit integer, clip it
    byte1 = code // 2 ** 12
    byte2 = (code % 2 ** 12) // 2 ** 4
    byte3 = (code - byte1 * 2 ** 12 - byte2 * 2 ** 4) * 2 ** 4
    return bytes([byte1, byte2, byte3])


def dac_bytes_to_decimal(dac_bytes):
    """Convert three data bytes in the DAC1220 format to a 20-bit number ranging from -2**19 to 2**19-1."""
    code = 2 ** 12 * dac_bytes[0] + 2 ** 4 * dac_bytes[1] + dac_bytes[2] / 2 ** 4
    return code - 2 ** 19


def cv_sweep(time_elapsed, ustart, ustop, ubound, lbound, scanrate, n):
    """Generate the potential profile for a cyclic voltammetry sweep.

    Keyword arguments:
    time_elapsed -- the elapsed time [s]
    ustart -- the start potential [V]
    ustop -- the stop potential [V]
    ubound -- the upper potential bound [V]
    lbound -- the lower potential bound [V]
    scanrate -- the scan rate [V/s]
    n -- the number of scans

    Returns the potential as a function of the elapsed time; if the elapsed time exceeds the end of the CV sweep, returns None.
    """
    global cv_cycle
    if scanrate < 0:  # The rest of the function assumes a positive scan rate; a negative one is handled here by recursion
        try:
            return -cv_sweep(time_elapsed, -ustart, -ustop, -lbound, -ubound, -scanrate,
                             n)  # Re-run the function with inverted potentials and scan rates and invert the result
        except TypeError:
            return None  # If the result of the inverted function is None, it cannot be inverted, so return None
    srt_0 = ubound - ustart  # Potential difference to traverse in the initial stage (before potential reaches upper bound)
    srt_1 = (
                    ubound - lbound) * 2. * n  # Potential difference to traverse in the "cyclic stage" (repeated scans from upper to lower bound and back)
    srt_2 = abs(
        ustop - ubound)  # Potential difference to traverse in the final stage (from upper bound to stop potential)
    srtime = scanrate * time_elapsed  # Linear potential sweep
    cv_duration = (srt_0 + srt_1 + srt_2) / scanrate
    if srtime < srt_0:  # Initial stage
        cv_cycle = 0
        return ustart + srtime
    elif srtime < srt_0 + srt_1:  # Cyclic stage
        srtime = srtime - srt_0
        cv_cycle = int((srtime / ((
                                          ubound - lbound) * 2)) + 1)  # uses the voltage covered so far, divided by the range, to figure out what cycle we're in. Because we want an int, and this rounds down, we add 1 to even it up
        return lbound + abs((srtime) % (2 * (ubound - lbound)) - (ubound - lbound))
    elif srtime < srt_0 + srt_1 + srt_2:  # Final stage
        srtime = srtime - srt_0 - srt_1
        if ustop > ubound:
            cv_cycle = n + 1
            return ubound + srtime
        else:
            cv_cycle = n + 1
            return ubound - srtime
    else:
        return None  # CV finished


def charge_from_cv(time_arr, current_arr):
    """Integrate current as a function of time to calculate charge between zero crossings."""
    zero_crossing_indices = []
    charge_arr = []
    running_index = 0
    while running_index < len(current_arr):
        counter = 0
        while running_index < len(current_arr) and current_arr[
            running_index] >= 0.:  # Iterate over a block of positive currents
            running_index += 1
            counter += 1
        if counter >= 10:  # Check if the block holds at least 10 values (this makes the counting immune to noise around zero crossings)
            zero_crossing_indices.append(
                running_index - counter)  # If so, append the index of the start of the block to the list of zero-crossing indices
        counter = 0
        while running_index < len(current_arr) and current_arr[
            running_index] <= 0.:  # Do the same for a block of negative currents
            running_index += 1
            counter += 1
        if counter >= 10:
            zero_crossing_indices.append(running_index - counter)
    for index in range(0, len(zero_crossing_indices) - 1):  # Go over all zero crossings
        zc_index1 = zero_crossing_indices[index]  # Start index
        zc_index2 = zero_crossing_indices[index + 1]  # End index
        charge_arr.append(numpy.trapz(current_arr[zc_index1:zc_index2], time_arr[
                                                                        zc_index1:zc_index2]) * 1000. / 3.6)  # Integrate current over time using the trapezoid rule, convert coulomb to uAh
    return charge_arr


def make_groupbox_indicator(title_name, default_text):
    """Make a GUI box (used for the potential, current, and status indicators)."""
    label = QtWidgets.QLabel(text=default_text, alignment=QtCore.Qt.AlignCenter)
    box = QtWidgets.QGroupBox(title=title_name, flat=False)
    format_box_for_display(box)
    layout = QtWidgets.QVBoxLayout()
    layout.addWidget(label, 0, alignment=QtCore.Qt.AlignCenter)
    layout.setSpacing(0)
    layout.setContentsMargins(30, 3, 30, 0)
    box.setLayout(layout)
    return label, box


def add_my_tab(tab_frame, tab_name):
    """Add a tab to the tab view."""
    widget = QtWidgets.QWidget()
    tab_frame.addTab(widget, tab_name)
    return widget


def format_box_for_display(box):
    """Adjust the appearance of a groupbox border for the status display."""
    color = box.palette().color(QtGui.QPalette.Background)  # Get the background color
    r, g, b = int(0.9 * color.red()), int(0.9 * color.green()), int(
        0.9 * color.blue())  # Make background 10% darker to make the border color
    box.setStyleSheet(
        "QGroupBox { border: 1px solid rgb(%d,%d,%d); border-radius: 4px; margin-top: 0.5em; font-weight: normal; color: gray;} QGroupBox::title {subcontrol-origin: margin; left: 10px; padding: 0 3px 0 3px;}" % (
            r, g, b))  # Apply the border


def format_box_for_parameter(box):
    """Adjust the appearance of a groupbox border for parameter input."""
    color = box.palette().color(QtGui.QPalette.Background)  # Get the background color
    r, g, b = int(0.7 * color.red()), int(0.7 * color.green()), int(
        0.7 * color.blue())  # Make background 30% darker to make the border color
    box.setStyleSheet(
        "QGroupBox { border: 1px solid rgb(%d,%d,%d); border-radius: 4px; margin-top: 0.5em; font-weight: bold} QGroupBox::title {subcontrol-origin: margin; left: 10px; padding: 0 3px 0 3px;}" % (
            r, g, b))  # Apply the border


def make_label_entry(parent, labelname):
    """Make a labelled input field for parameter input."""
    hbox = QtWidgets.QHBoxLayout()
    label = QtWidgets.QLabel(text=labelname)
    entry = QtWidgets.QLineEdit()
    hbox.addWidget(label)
    hbox.addWidget(entry)
    parent.addLayout(hbox)
    return entry


def make_radio_entry(parent, labelname):
    hbox = QtWidgets.QHBoxLayout()
    radio_button = QtWidgets.QRadioButton(text=labelname)
    hbox.addWidget(radio_button)
    parent.addLayout(hbox)
    return radio_button

def custom_size_font(fontsize):
    """Return the default Qt font with a custom point size."""
    myfont = QtGui.QFont()
    myfont.setPointSize(fontsize)
    return myfont


def log_message(message):
    """Log a string to the message log."""
    statustext.appendPlainText(datetime.datetime.now().strftime("[%Y-%m-%d %H:%M:%S] ") + message)
    statustext.ensureCursorVisible()


def usb_scan():
    """"Scan the USB and add them to a list for connecting to under USB Interface in the GUI"""
    usb_vid_string = str(usb_vid)
    usb_pid_string = str(usb_pid)
    usb_device_list.clear()
    hardware_usb_device_list_dropdown.clear()
    #print(usb_vid_string)
    for scanned_device in usb.core.find(idVendor=int(usb_vid_string, 0), idProduct=int(usb_pid_string, 0),
                                        find_all=True):
        try:
            usb_device_list.append(scanned_device.serial_number)
        except ValueError:
            pass

    if len(usb_device_list) == 0:
        usb_device_list.append('No Devices Found')
    usb_device_list.sort()
    hardware_usb_device_list_dropdown.addItems(usb_device_list)


def connect_disconnect_usb():
    """Toggle the USB device between connected and disconnected states."""
    global dev, state
    if dev is not None:  # If the device is already connected, then this function should disconnect it
        usb.util.dispose_resources(dev)
        dev = None
        state = States.NotConnected
        hardware_usb_connectButton.setText("Connect")
        log_message("USB Interface disconnected.")
        win.setWindowTitle('USB potentiostat/galvanostat')
        hardware_device_info_text.setText(
            "Manufacturer: \nProduct: \nSerial #: ")
        return
    # Otherwise, try to connect
    usb_vid_string = str(usb_vid)
    usb_pid_string = str(usb_pid)
    serial_index = hardware_usb_device_list_dropdown.currentIndex()  # this returns an index number -> 0,1,2,3...
    if usb_device_list[serial_index] == 'No Devices Found':
        QtWidgets.QMessageBox.critical(mainwidget, "USB Device Not Found",
                                   "No USB device was found with VID %s and PID %s. Verify the vendor/product ID and check the USB connection." % (
                                       usb_vid_string, usb_pid_string))
    for dev in usb.core.find(idVendor=int(usb_vid_string, 0), idProduct=int(usb_pid_string, 0), find_all=True):
        if dev is None:
            QtWidgets.QMessageBox.critical(mainwidget, "USB Device Not Found",
                                       "No USB device was found with VID %s and PID %s. Verify the vendor/product ID and check the USB connection." % (
                                           usb_vid_string, usb_pid_string))
        try:
            if dev.serial_number == usb_device_list[
                serial_index]:  # error here when lower number dev in use, and attempt access higher dev... no langid
                hardware_usb_connectButton.setText("Disconnect")
                log_message("USB Interface connected.")
                log_message(str(type(dev)))
                try:
                    hardware_device_info_text.setText(
                        "Manufacturer: %s\nProduct: %s\nSerial #: %s" % (
                            dev.manufacturer, dev.product, dev.serial_number))
                    win.setWindowTitle('USB potentiostat/galvanostat - Device: ' + dev.serial_number)
                    get_calibration()
                    set_cell_status(False)  # Cell off
                    set_control_mode(False)  # Potentiostatic control
                    set_current_range()  # Read current range from GUI
                    state = States.Idle_Init  # Start idle mode
                except ValueError:
                    pass  # In case the device is not yet calibrated
                break
            if dev.serial_number != usb_device_list[serial_index]:
                dev = None
                # print('skipped')
        except ValueError:
            # this section allows the device scan to bypass lower-serial-number devices that are in use
            pass
            # dev = None
            # print('ValueError - Langid Skip')


def not_connected_errormessage():
    """Generate an error message stating that the device is not connected."""
    QtWidgets.QMessageBox.critical(mainwidget, "Not connected",
                               "This command cannot be executed because the USB device is not connected. Press the \"Connect\" button and try again.")


def check_state(desired_states):
    """Check if the current state is in a given list. If so, return True; otherwise, show an error message and return False."""
    if state not in desired_states:
        if state == 0:
            not_connected_errormessage()
        else:
            QtWidgets.QMessageBox.critical(mainwidget, "Error", "This command cannot be executed in the current state.")
        return False
    else:
        return True


def send_command(command_string, expected_response, log_msg=None):
    """Send a command string to the USB device and check the response; optionally logs a message to the message log."""
    if dev is not None:  # Make sure it's connected
        dev.write(0x01, command_string)  # 0x01 = write address of EP1
        response = bytes(dev.read(0x81, 64))  # 0x81 = read address of EP1
        if response != expected_response:
            QtWidgets.QMessageBox.critical(mainwidget, "Unexpected Response",
                                       "The command \"%s\" resulted in an unexpected response. The expected response was \"%s\"; the actual response was \"%s\"" % (
                                           command_string, expected_response.decode("ascii"), response.decode("ascii")))
        else:
            if log_msg != None:
                log_message(log_msg)
        return True
    else:
        not_connected_errormessage()
        return False


def set_cell_status(cell_on_boolean):
    """Switch the cell connection (True = cell on, False = cell off)."""
    if cell_on_boolean:
        if send_command(b'CELL ON', b'OK'):
            cell_status_monitor.setText("CELL ON")
    else:
        if send_command(b'CELL OFF', b'OK'):
            cell_status_monitor.setText("CELL OFF")


def set_control_mode(galvanostatic_boolean):
    """Switch the control mode (True = galvanostatic, False = potentiostatic)."""
    global control_mode
    if galvanostatic_boolean:
        if send_command(b'GALVANOSTATIC', b'OK'):
            control_mode_monitor.setText("GALVANOSTATIC")
            control_mode = "GALVANOSTATIC"
    else:
        if send_command(b'POTENTIOSTATIC', b'OK'):
            control_mode_monitor.setText("POTENTIOSTATIC")
            control_mode = "POTENTIOSTATIC"


def set_current_range():
    """Switch the current range based on the GUI dropdown selection."""
    global currentrange
    index = hardware_manual_control_range_dropdown.currentIndex()
    commandstring = [b'RANGE 1', b'RANGE 2', b'RANGE 3'][index]
    if send_command(commandstring, b'OK'):
        current_range_monitor.setText(current_range_list[index])
        currentrange = index


def auto_current_range():
    """Automatically switch the current range based on the measured current; returns a number of measurements to skip (to suppress artifacts)."""
    global currentrange, overcounter, undercounter
    relativecurrent = abs(current / (20. / 100. ** currentrange))
    if relativecurrent > 1.05 and currentrange != 0 and cv_range_checkboxes[
        currentrange - 1].isChecked():  # Switch to higher current range (if possible) after three detections
        overcounter += 1
    else:
        overcounter = 0
    if relativecurrent < 0.0095 and currentrange != 2 and cv_range_checkboxes[
        currentrange + 1].isChecked():  # Switch to lower current range (if possible) after three detections
        undercounter += 1
    else:
        undercounter = 0
    if overcounter > 3:
        currentrange -= 1
        hardware_manual_control_range_dropdown.setCurrentIndex(currentrange)
        set_current_range()
        overcounter = 0
        return 2  # Skip next two measurements to suppress artifacts
    elif undercounter > 3:
        currentrange += 1
        hardware_manual_control_range_dropdown.setCurrentIndex(currentrange)
        set_current_range()
        undercounter = 0
        return 2  # Skip next two measurements to suppress artifacts
    else:
        return 0


def current_range_from_current(current):
    """Return the current range that best corresponds to a given current."""
    current = abs(current)
    if current <= 0.002:
        return 2  # Lowest current range (2 uA)
    elif current <= 0.2:
        return 1  # Intermediate current range (200 uA)
    else:
        return 0  # Highest current range (20 mA)


def get_next_enabled_current_range(desired_currentrange):
    """Return an enabled current range that best corresponds to a desired current range."""
    range_found = False
    found_currentrange = desired_currentrange
    for i in range(desired_currentrange, -1, -1):  # Look for an enabled current range, going up in current range
        if cv_range_checkboxes[i].isChecked():
            found_currentrange = i
            range_found = True
            break
    if not range_found:
        for i in range(desired_currentrange, 3):  # Look for an enabled current range, going down in current range
            if cv_range_checkboxes[i].isChecked():
                found_currentrange = i
                break
    return found_currentrange


def set_offset():
    """Save offset values to the device's flash memory."""
    send_command(b'OFFSETSAVE ' + decimal_to_dac_bytes(potential_offset) + decimal_to_dac_bytes(current_offset), b'OK',
                 "Offset values saved to flash memory.")


# noinspection PyUnresolvedReferences
def get_offset():
    """Retrieve offset values from the device's flash memory."""
    global potential_offset, current_offset
    if dev is not None:  # Make sure it's connected
        # noinspection PyUnresolvedReferences
        dev.write(0x01, b'OFFSETREAD')  # 0x01 = write address of EP1
        response = bytes(dev.read(0x81, 64))  # 0x81 = read address of EP1
        if response != bytes(
                [255, 255, 255, 255, 255, 255]):  # If no offset value has been stored, all bits will be set
            potential_offset = dac_bytes_to_decimal(response[0:3])
            current_offset = dac_bytes_to_decimal(response[3:6])
            hardware_calibration_potential_offset.setText("%d" % potential_offset)
            hardware_calibration_current_offset.setText("%d" % current_offset)
            log_message("Offset values read from flash memory.")
        else:
            log_message("No offset values were found in flash memory.")
    else:
        not_connected_errormessage()


def float_to_twobytes(value):
    """Convert a floating-point number ranging from -2^15 to 2^15-1 to a 16-bit representation stored in two bytes."""
    code = 2 ** 15 + int(round(value))
    code = numpy.clip(code, 0, 2 ** 16 - 1)  # If the code exceeds the boundaries of a 16-bit integer, clip it
    byte1 = code // 2 ** 8
    byte2 = code % 2 ** 8
    return bytes([byte1, byte2])


def twobytes_to_float(bytes_in):
    """Convert two bytes to a number ranging from -2^15 to 2^15-1."""
    code = 2 ** 8 * bytes_in[0] + bytes_in[1]
    return float(code - 2 ** 15)


def set_shunt_calibration():
    """Save shunt calibration values to the device's flash memory."""
    send_command(b'SHUNTCALSAVE ' + float_to_twobytes((shunt_calibration[0] - 1.) * 1e6) + float_to_twobytes(
        (shunt_calibration[1] - 1.) * 1e6) + float_to_twobytes((shunt_calibration[2] - 1.) * 1e6), b'OK',
                 "Shunt calibration values saved to flash memory.")


def get_shunt_calibration():
    """Retrieve shunt calibration values from the device's flash memory."""
    if dev is not None:  # Make sure it's connected
        dev.write(0x01, b'SHUNTCALREAD')  # 0x01 = write address of EP1
        response = bytes(dev.read(0x81, 64))  # 0x81 = read address of EP1
        if response != bytes(
                [255, 255, 255, 255, 255, 255]):  # If no calibration value has been stored, all bits are set
            for i in range(0, 3):
                shunt_calibration[i] = 1. + twobytes_to_float(
                    response[2 * i:2 * i + 2]) / 1e6  # Yields an adjustment range from 0.967 to 1.033 in steps of 1 ppm
                hardware_calibration_shuntvalues[i].setText("%.4f" % shunt_calibration[i])
            log_message("Shunt calibration values read from flash memory.")
        else:
            log_message("No shunt calibration values were found in flash memory.")
    else:
        not_connected_errormessage()


def zero_offset():
    """Calculate offset values in order to zero the potential and current."""
    if not check_state([States.Idle]):
        return  # Device needs to be in the idle state for this
    pot_offs = int(round(numpy.average(list(last_raw_potential_values))))  # Average potential offset
    cur_offs = int(round(numpy.average(list(last_raw_current_values))))  # Average current offset
    hardware_calibration_potential_offset.setText("%d" % pot_offs)
    hardware_calibration_current_offset.setText("%d" % cur_offs)
    offset_changed_callback()


def offset_changed_callback():
    """Set the potential and current offset from the input fields."""
    global potential_offset, current_offset
    try:
        potential_offset = int(hardware_calibration_potential_offset.text())
        hardware_calibration_potential_offset.setStyleSheet("")
    except ValueError:  # If the input field cannot be interpreted as a number, color it red
        hardware_calibration_potential_offset.setStyleSheet("QLineEdit { background: red; }")
    try:
        current_offset = int(hardware_calibration_current_offset.text())
        hardware_calibration_current_offset.setStyleSheet("")
    except ValueError:  # If the input field cannot be interpreted as a number, color it red
        hardware_calibration_current_offset.setStyleSheet("QLineEdit { background: red; }")


def shunt_calibration_changed_callback():
    """Set the shunt calibration values from the input fields."""
    for i in range(0, 3):
        try:
            shunt_calibration[i] = float(hardware_calibration_shuntvalues[i].text())
            hardware_calibration_shuntvalues[i].setStyleSheet("")
        except ValueError:  # If the input field cannot be interpreted as a number, color it red
            hardware_calibration_shuntvalues[i].setStyleSheet("QLineEdit { background: red; }")


def set_dac_calibration():
    """Save DAC calibration values to the DAC and the device's flash memory."""
    try:
        dac_offset = int(hardware_calibration_dac_offset.text())
        hardware_calibration_dac_offset.setStyleSheet("")
    except ValueError:  # If the input field cannot be interpreted as a number, color it red
        hardware_calibration_dac_offset.setStyleSheet("QLineEdit { background: red; }")
        return
    try:
        dac_gain = int(hardware_calibration_dac_gain.text())
        hardware_calibration_dac_gain.setStyleSheet("")
    except ValueError:  # If the input field cannot be interpreted as a number, color it red
        hardware_calibration_dac_gain.setStyleSheet("QLineEdit { background: red; }")
        return
    send_command(b'DACCALSET ' + decimal_to_dac_bytes(dac_offset) + decimal_to_dac_bytes(dac_gain - 2 ** 19), b'OK',
                 "DAC calibration saved to flash memory.")


def get_dac_calibration():
    """Retrieve DAC calibration values from the device's flash memory."""
    if dev is not None:  # Make sure it's connected
        dev.write(0x01, b'DACCALGET')  # 0x01 = write address of EP1
        response = bytes(dev.read(0x81, 64))  # 0x81 = write address of EP1
        if response != bytes(
                [255, 255, 255, 255, 255, 255]):  # If no calibration value has been stored, all bits are set
            dac_offset = dac_bytes_to_decimal(response[0:3])
            dac_gain = dac_bytes_to_decimal(response[3:6]) + 2 ** 19
            hardware_calibration_dac_offset.setText("%d" % dac_offset)
            hardware_calibration_dac_gain.setText("%d" % dac_gain)
            log_message("DAC calibration read from flash memory.")
        else:
            log_message("No DAC calibration values were found in flash memory.")
    else:
        not_connected_errormessage()


def set_calibration():
    """Save all calibration values to the device's flash memory."""
    set_dac_calibration()
    set_offset()
    set_shunt_calibration()


def get_calibration():
    """Retrieve all calibration values from the device's flash memory."""
    get_dac_calibration()
    get_offset()
    get_shunt_calibration()


def dac_calibrate():
    """Activate the automatic DAC1220 calibration function and retrieve the results."""
    send_command(b'DACCAL', b'OK', "DAC calibration performed.")
    get_dac_calibration()


def set_output(value_units_index, value):
    """Output data to the DAC; units can be either V (index 0), mA (index 1), or raw counts (index 2)."""
    if value_units_index == 0:
        send_command(b'DACSET ' + decimal_to_dac_bytes(value / 8. * 2. ** 19 + int(round(potential_offset / 4.))),
                     b'OK')
    elif value_units_index == 1:
        send_command(b'DACSET ' + decimal_to_dac_bytes(
            value / (25. / (shunt_calibration[currentrange] * 100. ** currentrange)) * 2. ** 19 + int(
                round(current_offset / 4.))), b'OK')
    elif value_units_index == 2:
        send_command(b'DACSET ' + decimal_to_dac_bytes(value), b'OK')


def set_output_from_gui():
    """Output data to the DAC from the GUI input field (hardware tab, manual control)."""
    value_units_index = hardware_manual_control_output_dropdown.currentIndex()
    if value_units_index == 0:  # Potential (V)
        try:
            value = float(hardware_manual_control_output_entry.text())
        except ValueError:
            QtWidgets.QMessageBox.critical(mainwidget, "Not a number",
                                       "The value you have entered is not a floating-point number.")
            return
    elif value_units_index == 1:  # Current (mA)
        try:
            value = float(hardware_manual_control_output_entry.text())
        except ValueError:
            QtWidgets.QMessageBox.critical(mainwidget, "Not a number",
                                       "The value you have entered is not a floating-point number.")
            return
    elif value_units_index == 2:  # DAC Code
        try:
            value = int(hardware_manual_control_output_entry.text())
        except ValueError:
            QtWidgets.QMessageBox.critical(mainwidget, "Not a number",
                                       "The value you have entered is not an integer number.")
            return
    else:
        return
    set_output(value_units_index, value)


def wait_for_adcread():
    """Wait for the duration specified in the busyloop_interval."""
    if busyloop_interval == 0:
        return  # On Linux/Mac, system timing is used instead of the busyloop
    else:
        time.sleep(busyloop_interval / 2.)  # Sleep for some time to prevent wasting too many CPU cycles
        app.processEvents()  # Update the GUI
        while timeit.default_timer() < time_of_last_adcread + busyloop_interval:
            pass  # Busy loop (this is the only way to get accurate timing on MS Windows)


def read_potential_current():
    """Read the most recent potential and current values from the device's ADC."""
    global potential, current, raw_potential, raw_current, time_of_last_adcread
    wait_for_adcread()
    time_of_last_adcread = timeit.default_timer()
    dev.write(0x01, b'ADCREAD')  # 0x01 = write address of EP1
    response = bytes(dev.read(0x81, 64))  # 0x81 = read address of EP1
    if response != b'WAIT':  # 'WAIT' is received if a conversion has not yet finished
        raw_potential = twocomplement_to_decimal(response[0], response[1], response[2])
        raw_current = twocomplement_to_decimal(response[3], response[4], response[5])
        potential = (
                            raw_potential - potential_offset) / 2097152. * 8.  # Calculate potential in V, compensating for offset
        current = (raw_current - current_offset) / 2097152. * 25. / (shunt_calibration[
                                                                         currentrange] * 100. ** currentrange)  # Calculate current in mA, taking current range into account and compensating for offset
        potential_monitor.setText(potential_to_string(potential))
        current_monitor.setText(current_to_string(currentrange, current))
        if logging_enabled:  # If enabled, all measurements are appended to an output file (even in idle mode)
            try:
                print("%.2f\t%e\t%e" % (time_of_last_adcread, potential, current * 1e-3),
                      file=open(hardware_log_filename.text(), 'a',
                                1))  # Output tab-separated data containing time (in s), potential (in V), and current (in A)
            except:
                QtWidgets.QMessageBox.critical(mainwidget, "Logging error!", "Logging error!")
                hardware_log_checkbox.setChecked(False)  # Disable logging in case of file errors


def idle_init():
    """Perform some necessary initialization before entering the Idle state."""
    global potential_plot_curve, current_plot_curve, legend, state
    plot_frame.clear()
    try:
        legend.scene().removeItem(legend)  # Remove any previous legends
    except AttributeError:
        pass  # In case the legend was already removed
    except NameError:
        pass  # In case a legend has never been created
    plot_frame.setLabel('bottom', 'Sample #', units="")
    plot_frame.setLabel('left', 'Value', units="")
    legend = plot_frame.addLegend()
    plot_frame.enableAutoRange()
    plot_frame.setXRange(0, 200, update=True)
    potential_plot_curve = plot_frame.plot(pen='g', name='Potential (V)')
    current_plot_curve = plot_frame.plot(pen='r', name='Current (mA)')
    state = States.Idle  # Proceed to the Idle state


def update_live_graph():
    """Add newly measured potential and current values to their respective buffers and update the plot curves."""
    last_potential_values.append(potential)
    last_current_values.append(current)
    last_raw_potential_values.append(raw_potential)
    last_raw_current_values.append(raw_current)
    xvalues = range(last_potential_values.maxlen - len(last_potential_values), last_potential_values.maxlen)
    potential_plot_curve.setData(xvalues, list(last_potential_values))
    current_plot_curve.setData(xvalues, list(last_current_values))


def choose_file(file_entry_field, questionstring):
    """Open a file dialog and write the path of the selected file to a given entry field."""
    filedialog = QtWidgets.QFileDialog()
    # file_entry_field.setText(filedialog.getSaveFileName(mainwidget, questionstring, "", "ASCII data (*.txt)", options=QtGui.QFileDialog.DontConfirmOverwrite))  #original code
    # ---------------------------------my code---------------------------------
    tempdirectory = filedialog.getSaveFileName(mainwidget, questionstring, "",
                                               "ASCII data (*.txt)")  # , options=QtGui.QFileDialog.DontConfirmOverwrite) #reenabling overwrite confirmation
    file_entry_field.setText(tempdirectory[0])  # getSaveFileName returns a tuple, so access first element!
    # ---------------------------------my code---------------------------------

#
# def add_test(widget_list, test):
#     widget_list.addItem(test)


def remove_test(widget_list, index):
    if len(widget_list) > 0:
        for i in test_sequence.keys():
            # print(widget_list.item(index).text())
            if test_sequence[i]["filename"] == widget_list.item(index).text():
                key_id = i
        widget_list.takeItem(index)
        del test_sequence[key_id]
        # i = 0
        # for id in test_sequence:
        #     test_sequence[id]['test_key'] = i
        #     i = i + 1


def seq_list_changed():
    global sequence_index, sequence_test_list, test_sequence
    sequence_index = 0
    temp_sequence = {}
    for row in range(0, len(sequence_test_list)):
        list_filename = sequence_test_list.item(row).text()
        # print(list_filename)
        for key in test_sequence:
            if test_sequence[key]["filename"] == list_filename:
                test_sequence[key]["test_key"] = row
                temp_sequence[row] = test_sequence[key]
    test_sequence = temp_sequence



def confirm_test():
    global sequence_index, sequence_test_list, test_sequence
    sequence_index = 0
    temp_sequence = {}
    i = 0
    # for key in test_sequence:
    #     test_sequence[key]['test_key'] = i
    #     i = i + 1
    # print(f"pre-sort: {test_sequence}")
    for row in range(0, len(sequence_test_list)):
        list_filename = sequence_test_list.item(row).text()
        # print(list_filename)
        for key in test_sequence:
            if test_sequence[key]["filename"] == list_filename:
                test_sequence[key]["test_key"] = row
                temp_sequence[row] = test_sequence[key]
    test_sequence = temp_sequence
    for key in test_sequence:
        if not validate_file(test_sequence[key]["filename"]):
            return
    # print(f"post-sort: {test_sequence}")
    sequence_start_button.setEnabled(True)
    sequence_test_add_button.setEnabled(False)
    sequence_test_remove_button.setEnabled(False)
    sequence_cvradio_entry.setEnabled(False)
    sequence_cdradio_entry.setEnabled(False)
    sequence_rateradio_entry.setEnabled(False)
    sequence_ocvradio_entry.setEnabled(False)


def choose_directory(directory_entry_field, questionstring):
    directorydialog = QtWidgets.QFileDialog()
    tempdirectory = directorydialog.getExistingDirectory(None, questionstring)
    directory_entry_field.setText(tempdirectory)


def toggle_logging(checkbox_state):
    """Enable or disable logging of measurements to a file based on the state of a checkbox (2 means checked)."""
    global logging_enabled
    logging_enabled = (checkbox_state == 2)


def toggle_error_logging(checkbox_state):
    """Enable or disable error logging from STDOUT and STDERR to logfile"""
    global usb_debug_flag
    usb_debug_flag = (checkbox_state == 2)


def toggle_voltage_finish(checkbox_state):
    """Enable or disable constant voltage finishing during constant current tests"""
    global cd_voltage_finish_flag
    # print("toggle_voltage_finish")
    if cd_voltage_finish_flag == True:
        cd_voltage_finish_flag = False
        voltage_finish_time_radio.setEnabled(False)
        voltage_finish_current_radio.setEnabled(False)
        voltage_finish_time_entry.setEnabled(False)
        voltage_finish_chargecurrent_entry.setEnabled(False)
        voltage_finish_dischargecurrent_entry.setEnabled(False)
        voltage_finish_chargecurrent_entry.setText("")
        voltage_finish_dischargecurrent_entry.setText("")
        voltage_finish_time_entry.setText("")
        voltage_finish_both_radio.setEnabled(False)
    if checkbox_state == 2:
        cd_voltage_finish_flag = True
        voltage_finish_time_radio.setEnabled(True)
        voltage_finish_current_radio.setEnabled(True)
        voltage_finish_time_entry.setEnabled(True)
        voltage_finish_time_entry.setText("")
        voltage_finish_both_radio.setEnabled(True)


def set_voltage_finish_mode():
    global cd_voltage_finish_mode
    if voltage_finish_time_radio.isChecked():
        cd_voltage_finish_mode = 0
        # print("voltage finish mode", cd_voltage_finish_mode)
        voltage_finish_time_entry.setText("")
        voltage_finish_chargecurrent_entry.setText("")
        voltage_finish_dischargecurrent_entry.setText("")
        voltage_finish_time_entry.setEnabled(False)
        voltage_finish_time_entry.setEnabled(True)
        voltage_finish_chargecurrent_entry.setEnabled(False)
        voltage_finish_dischargecurrent_entry.setEnabled(False)
    if voltage_finish_current_radio.isChecked():
        cd_voltage_finish_mode = 1
        # print("voltage finish mode", cd_voltage_finish_mode)
        voltage_finish_time_entry.setText("")
        voltage_finish_chargecurrent_entry.setText("")
        voltage_finish_dischargecurrent_entry.setText("")
        voltage_finish_time_entry.setEnabled(False)
        voltage_finish_chargecurrent_entry.setEnabled(False)
        voltage_finish_dischargecurrent_entry.setEnabled(False)
        voltage_finish_chargecurrent_entry.setEnabled(True)
        voltage_finish_dischargecurrent_entry.setEnabled(True)
    if voltage_finish_both_radio.isChecked():
        cd_voltage_finish_mode = 2
        # print("voltage finish mode", cd_voltage_finish_mode)
        # voltage_finish_time_entry.setText("")
        # voltage_finish_current_entry.setText("")
        voltage_finish_time_entry.setEnabled(True)
        voltage_finish_chargecurrent_entry.setEnabled(True)
        voltage_finish_dischargecurrent_entry.setEnabled(True)
    else:
        pass


def cv_getparams():
    """Retrieve the CV parameters from the GUI input fields and store them in a global dictionary. If succesful, return True."""
    global cv_parameters
    try:
        cv_parameters['lbound'] = float(cv_lbound_entry.text())
        cv_parameters['ubound'] = float(cv_ubound_entry.text())
        cv_parameters['startpot'] = float(cv_startpot_entry.text())
        cv_parameters['stoppot'] = float(cv_stoppot_entry.text())
        cv_parameters['scanrate'] = float(cv_scanrate_entry.text()) / 1e3  # Convert to V/s
        cv_parameters['numcycles'] = int(cv_numcycles_entry.text())
        cv_parameters['numsamples'] = int(cv_numsamples_entry.text())
        cv_parameters['filename'] = str(cv_file_entry.text())
        return True
    except ValueError:
        QtWidgets.QMessageBox.critical(mainwidget, "Not a number",
                                   "One or more parameters could not be interpreted as a number.")
        return False


def cv_validate_parameters():
    """Check if the chosen CV parameters make sense. If so, return True."""
    if cv_parameters['ubound'] < cv_parameters['lbound']:
        QtWidgets.QMessageBox.critical(mainwidget, "CV error", "The upper bound cannot be lower than the lower bound.")
        return False
    if cv_parameters['scanrate'] == 0:
        QtWidgets.QMessageBox.critical(mainwidget, "CV error", "The scan rate cannot be zero.")
        return False
    if (cv_parameters['scanrate'] > 0) and (cv_parameters['ubound'] < cv_parameters['startpot']):
        QtWidgets.QMessageBox.critical(mainwidget, "CV error",
                                   "For a positive scan rate, the start potential must be lower than the upper bound.")
        return False
    if (cv_parameters['scanrate'] < 0) and (cv_parameters['lbound'] > cv_parameters['startpot']):
        QtWidgets.QMessageBox.critical(mainwidget, "CV error",
                                   "For a negative scan rate, the start potential must be higher than the lower bound.")
        return False
    if cv_parameters['numsamples'] < 1:
        QtWidgets.QMessageBox.critical(mainwidget, "CV error", "The number of samples to average must be at least 1.")
        return False
    return True


def validate_file(filename, overwrite_protect=True):
    """Check if a filename can be written to. If so, return True."""
    if os.path.isfile(filename):
        if overwrite_protect:
            if QtWidgets.QMessageBox.question(mainwidget, "File exists",
                                          "The specified output file already exists. Do you want to overwrite it?",
                                          QtWidgets.QMessageBox.Yes | QtWidgets.QMessageBox.No,
                                          QtWidgets.QMessageBox.No) != QtWidgets.QMessageBox.Yes:
                return False
    try:
        tryfile = open(filename, 'w', 1)
        tryfile.close()
        return True
    except IOError:
        QtWidgets.QMessageBox.critical(mainwidget, "File error", "The specified output file path is not valid.")
        return False


def cv_scanrate_changed_callback():
    """Calculate a suggested number of samples to average based on the entered value for the CV scan rate."""
    try:
        cv_scanrate = float(cv_scanrate_entry.text())
        numsamples = int(20. / abs(
            cv_scanrate)) + 1  # Aims for approx. one (averaged) measurement every 2 to 4 mV for scan rates up to 20 mV/s
        cv_numsamples_entry.setText("%d" % numsamples)
    except:
        pass  # Don't do anything in case the entered scan rate value is invalid


def cv_numcycles_changed_callback():
    try:
        global cv_duration
        initialtime = float(cv_ubound_entry.text()) - float(cv_startpot_entry.text())
        cycletime = (float(cv_ubound_entry.text()) - float(cv_lbound_entry.text())) * 2. * int(
            cv_numcycles_entry.text())
        finaltime = abs(float(cv_stoppot_entry.text()) - float(cv_ubound_entry.text()))
        cv_duration = (initialtime + cycletime + finaltime) / (float(cv_scanrate_entry.text()) / 1000)
        cv_duration_text = duration_to_text_days_hours(cv_duration)
        cv_time_calculator_text.setText(f"Duration: {cv_duration_text}\nStart: \nEst. End: ")
    except:
        pass


def duration_to_text_days_hours(test_duration):
    try:
        test_duration_days = int(test_duration / (3600 * 24))
        test_duration_hours = (test_duration - (test_duration_days * (3600 * 24))) / 3600
        test_duration_text = f'{test_duration_days} days, {test_duration_hours:.2f} hours'
        return test_duration_text
    except:
        pass


def cv_start():
    """Initialize the CV measurement."""
    global cv_time_data, cv_potential_data, cv_current_data, cv_plot_curve, cv_outputfile, state, skipcounter, cv_parameters, test_start, test_end
    if check_state(
            [States.Idle, States.Stationary_Graph]) and cv_getparams() and cv_validate_parameters() and validate_file(
        cv_parameters['filename']):
        test_start = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        cv_duration_text = duration_to_text_days_hours(cv_duration)
        test_end = datetime.datetime.now() + datetime.timedelta(seconds=cv_duration)
        cv_end_text = test_end.strftime("%Y-%m-%d %H:%M:%S")
        cv_time_calculator_text.setText(f"Duration: {cv_duration_text}\nStart: {test_start}\nEst. End: {cv_end_text} ")
        cv_outputfile = open(cv_parameters['filename'], 'w', 1)  # 1 means line-buffered
        # do not change spacing below - it will change the fileheader
        cv_outputfile.write(
            f"""Device Serial:\t{dev.serial_number}
Estimated Duration[s]:\t{cv_duration}
Start Time:\t{test_start}
Estimated End:\t{cv_end_text}
Lower Bound[V]:\t{cv_parameters['lbound']}
Upper Bound[V]:\t{cv_parameters['ubound']}
Start Voltage[V]:\t{cv_parameters['startpot']}
Stop Voltage[V]:\t{cv_parameters['stoppot']}
Scan Rate[V/s]:\t{cv_parameters['scanrate']}
Cycles:\t{cv_parameters['numcycles']}
Samples to Average:\t{cv_parameters['numsamples']}

Elapsed_Time(s)\tPotential(V)\tCurrent(A)\tCycle\n"""
        )
        set_output(0, cv_parameters['startpot'])
        set_control_mode(False)  # Potentiostatic control
        hardware_manual_control_range_dropdown.setCurrentIndex(0)  # Start at highest current range
        set_current_range()
        time.sleep(.1)  # Allow DAC some time to settle
        cv_time_data = AverageBuffer(cv_parameters['numsamples'])  # Holds averaged data for elapsed time
        cv_potential_data = AverageBuffer(cv_parameters['numsamples'])  # Holds averaged data for potential
        cv_current_data = AverageBuffer(cv_parameters['numsamples'])  # Holds averaged data for current
        set_cell_status(True)  # Cell on
        time.sleep(.1)  # Allow feedback loop some time to settle
        read_potential_current()
        time.sleep(.1)
        read_potential_current()  # Two reads are necessary because each read actually returns the result of the previous conversion
        hardware_manual_control_range_dropdown.setCurrentIndex(get_next_enabled_current_range(
            current_range_from_current(current)))  # Autorange based on the measured current
        set_current_range()
        time.sleep(.1)
        read_potential_current()
        time.sleep(.1)
        read_potential_current()
        hardware_manual_control_range_dropdown.setCurrentIndex(
            get_next_enabled_current_range(current_range_from_current(current)))  # Another autorange, just to be sure
        set_current_range()
        preview_cancel_button.hide()
        try:  # Set up the plotting area
            legend.scene().removeItem(legend)
        except AttributeError:
            pass
        plot_frame.clear()
        plot_frame.enableAutoRange()
        plot_frame.setLabel('bottom', 'Potential', units="V")
        plot_frame.setLabel('left', 'Current', units="A")
        cv_plot_curve = plot_frame.plot(pen=pen_color[0])  # Plot first cycle CV in yellow, changes with cycle number
        log_message("CV measurement started. Saving to: %s" % cv_parameters['filename'])
        state = States.Measuring_CV
        skipcounter = 2  # Skip first two data points to suppress artifacts
        cv_parameters['starttime'] = timeit.default_timer()


def seq_cv_start():
    """Initialize the CV measurement."""
    global cv_time_data, cv_potential_data, cv_current_data, cv_plot_curve, cv_outputfile, state, skipcounter, cv_parameters, test_start, test_end
    # print("seq_cv_start")
    if check_state(
            [States.Idle, States.Stationary_Graph, States.Sequence_Idle]) and sequence_flag and cv_validate_parameters() and validate_file(
        cv_parameters['filename'], overwrite_protect=False):
        seq_test_start = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")

        initialtime = cv_parameters['ubound'] - cv_parameters['startpot']
        cycletime = (cv_parameters['ubound'] - cv_parameters['lbound']) * 2. * cv_parameters['numcycles']
        finaltime = abs(cv_parameters['stoppot'] - cv_parameters['ubound'])
        cv_parameters['duration'] = (initialtime + cycletime + finaltime) / (cv_parameters['scanrate'])# / 1000)

        cv_duration_text = duration_to_text_days_hours(cv_parameters['duration'])
        seq_test_end = datetime.datetime.now() + datetime.timedelta(seconds=cv_parameters['duration'])
        seq_cv_end_text = seq_test_end.strftime("%Y-%m-%d %H:%M:%S")
        # seq_cv_time_calculator_text.setText(
        #     f"Duration: {cv_duration_text}\nStart: {seq_test_start}\nEst. End: {seq_cv_end_text} ")
        cv_outputfile = open(cv_parameters['filename'], 'w', 1)  # 1 means line-buffered
        # do not change spacing below - it will change the fileheader
        cv_outputfile.write(
            f"""Device Serial:\t{dev.serial_number}
Estimated Duration[s]:\t{cv_parameters['duration']}
Start Time:\t{seq_test_start}
Estimated End:\t{seq_cv_end_text}
Lower Bound[V]:\t{cv_parameters['lbound']}
Upper Bound[V]:\t{cv_parameters['ubound']}
Start Voltage[V]:\t{cv_parameters['startpot']}
Stop Voltage[V]:\t{cv_parameters['stoppot']}
Scan Rate[V/s]:\t{cv_parameters['scanrate']}
Cycles:\t{cv_parameters['numcycles']}
Samples to Average:\t{cv_parameters['numsamples']}

Elapsed_Time(s)\tPotential(V)\tCurrent(A)\tCycle\n"""
        )
        set_output(0, cv_parameters['startpot'])
        set_control_mode(False)  # Potentiostatic control
        hardware_manual_control_range_dropdown.setCurrentIndex(0)  # Start at highest current range
        set_current_range()
        time.sleep(.1)  # Allow DAC some time to settle
        cv_time_data = AverageBuffer(cv_parameters['numsamples'])  # Holds averaged data for elapsed time
        cv_potential_data = AverageBuffer(cv_parameters['numsamples'])  # Holds averaged data for potential
        cv_current_data = AverageBuffer(cv_parameters['numsamples'])  # Holds averaged data for current
        set_cell_status(True)  # Cell on
        time.sleep(.1)  # Allow feedback loop some time to settle
        read_potential_current()
        time.sleep(.1)
        read_potential_current()  # Two reads are necessary because each read actually returns the result of the previous conversion
        hardware_manual_control_range_dropdown.setCurrentIndex(get_next_enabled_current_range(
            current_range_from_current(current)))  # Autorange based on the measured current
        set_current_range()
        time.sleep(.1)
        read_potential_current()
        time.sleep(.1)
        read_potential_current()
        hardware_manual_control_range_dropdown.setCurrentIndex(
            get_next_enabled_current_range(current_range_from_current(current)))  # Another autorange, just to be sure
        set_current_range()
        preview_cancel_button.hide()
        try:  # Set up the plotting area
            legend.scene().removeItem(legend)
        except AttributeError:
            pass
        plot_frame.clear()
        plot_frame.enableAutoRange()
        plot_frame.setLabel('bottom', 'Potential', units="V")
        plot_frame.setLabel('left', 'Current', units="A")
        cv_plot_curve = plot_frame.plot(pen=pen_color[0])  # Plot first cycle CV in yellow, changes with cycle number
        log_message("CV measurement started. Saving to: %s" % cv_parameters['filename'])
        state = States.Measuring_CV
        skipcounter = 2  # Skip first two data points to suppress artifacts
        cv_parameters['starttime'] = timeit.default_timer()


def cv_update():
    """Add a new data point to the CV measurement (should be called regularly)."""
    global state, skipcounter
    elapsed_time = timeit.default_timer() - cv_parameters['starttime']
    cv_output = cv_sweep(elapsed_time, cv_parameters['startpot'], cv_parameters['stoppot'], cv_parameters['ubound'],
                         cv_parameters['lbound'], cv_parameters['scanrate'], cv_parameters['numcycles'])
    if cv_output == None:  # This signifies the end of the CV scan
        cv_stop(interrupted=False)
    else:
        set_output(0, cv_output)  # Output a new potential value
        read_potential_current()  # Read new potential and current
        if skipcounter == 0:  # Process new measurements
            cv_time_data.add_sample(elapsed_time)
            cv_potential_data.add_sample(potential)
            cv_current_data.add_sample(1e-3 * current)  # Convert from mA to A
            if len(cv_time_data.samples) == 0 and len(
                    cv_time_data.averagebuffer) > 0:  # Check if a new average was just calculated
                # cv_outputfile.write("%e\t%e\t%e\t%s\n" % (
                #    cv_time_data.averagebuffer[-1], cv_potential_data.averagebuffer[-1],
                #    cv_current_data.averagebuffer[-1],
                #    cv_cycle))
                cv_outputfile.write(
                    f"{cv_time_data.averagebuffer[-1]:e}\t"
                    f"{cv_potential_data.averagebuffer[-1]:e}\t"
                    f"{cv_current_data.averagebuffer[-1]:e}\t"
                    f"{cv_cycle}\n"
                )
                cv_plot_curve.pen = pen_color[cv_cycle % len(pen_color)]  # Change color of CV curve
                cv_plot_curve.setData(cv_potential_data.averagebuffer,
                                      cv_current_data.averagebuffer)  # Update the graph
            skipcounter = auto_current_range()  # Update the graph
        else:  # Wait until the required number of data points is skipped
            skipcounter -= 1


def cv_stop(interrupted=True):
    """Finish the CV measurement."""
    global state, seq_cv_ocv_flag, sequence_index, sequence_flag
    sequence_index += 1
    seq_cv_ocv_flag = False
    if check_state([States.Measuring_CV]):
        set_cell_status(False)  # Cell off
        cv_outputfile.close()
        charge_arr = charge_from_cv(cv_time_data.averagebuffer,
                                    cv_current_data.averagebuffer)  # Integrate current between zero crossings to produce list of inserted/extracted charges
        if interrupted:
            log_message("CV measurement interrupted. Calculated charges (in uAh): [" + ', '.join(
                "%.2f" % value for value in
                charge_arr) + "]")  # Show calculated charges in the message log
        else:
            log_message("CV measurement finished. Calculated charges (in uAh): [" + ', '.join(
                "%.2f" % value for value in
                charge_arr) + "]")  # Show calculated charges in the message log
        if sequence_flag == False:
            state = States.Stationary_Graph  # Keep displaying the last plot until the user clicks a button
            preview_cancel_button.show()
        if sequence_flag == True:
            state = States.Sequence_Idle
        GraphAutoExport(plot_frame, cv_parameters['filename'])

def cv_preview():
    """Generate a preview of the CV potential profile in the plot window, based on the CV parameters currently entered in the GUI."""
    global state
    if check_state([States.Idle, States.Stationary_Graph]) and cv_getparams() and cv_validate_parameters():
        time_arr = []  # Initialize time array
        potential_arr = []  # Initialize potential array
        timeval = 0.  # Initialize elapsed time
        timestep = abs((cv_parameters['ubound'] - cv_parameters['lbound']) / 100. / cv_parameters[
            'scanrate'])  # Automatic timestep calculation, resulting in 100 potential steps between lower and upper bound
        cv_val = cv_sweep(timeval, cv_parameters['startpot'], cv_parameters['stoppot'], cv_parameters['ubound'],
                          cv_parameters['lbound'], cv_parameters['scanrate'], cv_parameters['numcycles'])
        while cv_val != None:  # Fill time and potential arrays with calculated values, loop until end of CV profile
            time_arr.append(timeval)
            potential_arr.append(cv_val)
            timeval += timestep
            cv_val = cv_sweep(timeval, cv_parameters['startpot'], cv_parameters['stoppot'], cv_parameters['ubound'],
                              cv_parameters['lbound'], cv_parameters['scanrate'], cv_parameters['numcycles'])
        try:
            legend.scene().removeItem(legend)
        except AttributeError:
            pass
        plot_frame.clear()
        plot_frame.enableAutoRange()
        plot_frame.setLabel('bottom', 'Time', units='s')
        plot_frame.setLabel('left', 'Potential', units='V')
        plot_frame.plot(time_arr, potential_arr, pen='g')
        preview_cancel_button.show()
        state = States.Stationary_Graph  # Keep displaying the CV preview until the user clicks a button


def preview_cancel():
    """Cancel the preview (stationary graph) state and go back to the idle state."""
    global state
    state = States.Idle_Init
    preview_cancel_button.hide()


def cv_get_ocp():
    """Insert the currently measured (open-circuit) potential into the start potential input field."""
    cv_startpot_entry.setText('%5.3f' % potential)
    return potential


def cd_getparams():
    """Retrieve the charge/discharge parameters from the GUI input fields and store them in a global dictionary. If succesful, return True."""
    global cd_parameters, cd_voltage_finish_flag, cd_voltage_finish_mode
    try:
        cd_parameters['lbound'] = float(cd_lbound_entry.text())
        cd_parameters['ubound'] = float(cd_ubound_entry.text())
        cd_parameters['chargecurrent'] = float(cd_chargecurrent_entry.text()) / 1e3  # convert uA to mA
        cd_parameters['dischargecurrent'] = float(cd_dischargecurrent_entry.text()) / 1e3  # convert uA to mA
        cd_parameters['numcycles'] = int(cd_numcycles_entry.text())
        cd_parameters['numsamples'] = int(cd_numsamples_entry.text())
        cd_parameters['filename'] = str(cd_file_entry.text())
        cd_parameters['finish_duration'] = 0
        cd_parameters['chargecurrent_duration'] = 0
        cd_parameters['dischargecurrent_duration'] = 0
        cd_parameters['voltage_finish_flag'] = cd_voltage_finish_flag
        cd_parameters['voltage_finish_mode'] = cd_voltage_finish_mode
        if cd_parameters['voltage_finish_flag']: #if cd_voltage_finish_flag:
            if cd_parameters['voltage_finish_mode'] == 0: #if cd_voltage_finish_mode == 0:
                cd_parameters['finish_duration'] = int(voltage_finish_time_entry.text())
                cd_parameters['chargecurrent_duration'] = 0
                cd_parameters['dischargecurrent_duration'] = 0
                # print("cd mode 0 - cd_getparams")
                # print(cd_parameters['finish_duration'])
            elif cd_parameters['voltage_finish_mode'] == 1:  #elif cd_voltage_finish_mode == 1:
                cd_parameters['finish_duration'] = 0
                cd_parameters['chargecurrent_duration'] = float(voltage_finish_chargecurrent_entry.text()) / 1e3
                cd_parameters['dischargecurrent_duration'] = float(voltage_finish_dischargecurrent_entry.text()) / 1e3
                # print("cd mode 1 - cd_getparams")
            elif cd_parameters['voltage_finish_mode'] == 2:  #elif cd_voltage_finish_mode == 2:
                cd_parameters['chargecurrent_duration'] = float(voltage_finish_chargecurrent_entry.text()) / 1e3
                cd_parameters['dischargecurrent_duration'] = float(voltage_finish_dischargecurrent_entry.text()) / 1e3
                cd_parameters['finish_duration'] = int(voltage_finish_time_entry.text())
                # print("cd mode 2 - cd_getparams")
        return True
    except ValueError:
        QtWidgets.QMessageBox.critical(mainwidget, "Not a number",
                                   "One or more parameters could not be interpreted as a number.")
        return False


def cd_validate_parameters():
    # print(f"State: {state}")
    # print(cd_parameters)
    """Check if the chosen charge/discharge parameters make sense. If so, return True."""
    if cd_parameters['ubound'] < cd_parameters['lbound']:
        QtWidgets.QMessageBox.critical(mainwidget, "Charge/discharge error",
                                   "The upper bound cannot be lower than the lower bound.")
        return False
    if cd_parameters['numcycles'] <= 0:
        QtWidgets.QMessageBox.critical(mainwidget, "Charge/discharge error",
                                   "The number of half cycles must be positive and non-zero.")
        return False
    if cd_parameters['numsamples'] < 1:
        QtWidgets.QMessageBox.critical(mainwidget, "Charge/discharge error",
                                   "The number of samples to average must be at least 1.")
        return False
    if cd_parameters['voltage_finish_flag']: #if cd_voltage_finish_flag:
        # print(f"cd_validate_parameters VF Flag: {cd_parameters['voltage_finish_flag']}")
        # print(f"cd_validate_parameters VF Mode: {cd_parameters['voltage_finish_mode']}")
        if cd_parameters['voltage_finish_mode'] == 0: #if cd_voltage_finish_mode == 0:
            if cd_parameters['finish_duration'] <= 0:
                QtWidgets.QMessageBox.critical(mainwidget, "Charge/discharge error",
                                           "Mode 0: The time for the voltage finish must be positive and non-zero.")
                return False
        elif cd_parameters['voltage_finish_mode'] == 1:  #elif cd_voltage_finish_mode == 1:
            if cd_parameters['chargecurrent'] > 0:
                if cd_parameters['chargecurrent_duration'] <= 0:
                    QtWidgets.QMessageBox.critical(mainwidget, "Charge/discharge error",
                                               "Mode 1: The sign for the voltage finish charge must match the sign of the charge current.")
                    return False
            if cd_parameters['chargecurrent'] < 0:
                if cd_parameters['chargecurrent_duration'] >= 0:
                    QtWidgets.QMessageBox.critical(mainwidget, "Charge/discharge error",
                                               "Mode 1: The sign for the voltage finish charge must match the sign of the charge current.")
                    return False
            if cd_parameters['dischargecurrent'] > 0:
                if cd_parameters['dischargecurrent_duration'] <= 0:
                    QtWidgets.QMessageBox.critical(mainwidget, "Charge/discharge error",
                                               "Mode 1: The sign for the voltage finish discharge must match the sign of the discharge current.")
                    return False
            if cd_parameters['dischargecurrent'] < 0:
                if cd_parameters['dischargecurrent_duration'] >= 0:
                    QtWidgets.QMessageBox.critical(mainwidget, "Charge/discharge error",
                                               "Mode 1: The sign for the voltage finish discharge must match the sign of the discharge current.")
                    return False
            if cd_parameters['chargecurrent_duration'] * cd_parameters['dischargecurrent_duration'] > 0:
                QtWidgets.QMessageBox.critical(mainwidget, "Charge/discharge error",
                                           "Mode 1: The charge and discharge duration must have opposite sign.")
                return False

        elif cd_parameters['voltage_finish_mode'] == 2:  #elif cd_voltage_finish_mode == 2:
            if cd_parameters['chargecurrent'] > 0:
                if cd_parameters['chargecurrent_duration'] <= 0:
                    QtWidgets.QMessageBox.critical(mainwidget, "Charge/discharge error",
                                               "Mode 2: The sign for the voltage finish charge must match the sign of the charge current.")
                    return False
            if cd_parameters['chargecurrent'] < 0:
                if cd_parameters['chargecurrent_duration'] >= 0:
                    QtWidgets.QMessageBox.critical(mainwidget, "Charge/discharge error",
                                               "Mode 2: The sign for the voltage finish charge must match the sign of the charge current.")
                    return False
            if cd_parameters['dischargecurrent'] > 0:
                if cd_parameters['dischargecurrent_duration'] <= 0:
                    QtWidgets.QMessageBox.critical(mainwidget, "Charge/discharge error",
                                               "Mode 2: The sign for the voltage finish discharge must match the sign of the discharge current.")
                    return False
            if cd_parameters['dischargecurrent'] < 0:
                if cd_parameters['dischargecurrent_duration'] >= 0:
                    QtWidgets.QMessageBox.critical(mainwidget, "Charge/discharge error",
                                               "Mode 2: The sign for the voltage finish discharge must match the sign of the discharge current.")
                    return False
            if cd_parameters['chargecurrent_duration'] * cd_parameters['dischargecurrent_duration'] > 0:
                QtWidgets.QMessageBox.critical(mainwidget, "Charge/discharge error",
                                           "Mode 2: The charge and discharge duration must have opposite sign.")
                return False
            if cd_parameters['finish_duration'] <= 0:
                QtWidgets.QMessageBox.critical(mainwidget, "Charge/discharge error",
                                           "Mode 2: The time for the voltage finish must be positive and non-zero.")
                return False
    return True


def cd_start():
    """Initialize the charge/discharge measurement."""
    global cd_charges, cd_currentsetpoint, cd_starttime, cd_currentcycle, cd_time_data, cd_potential_data, cd_current_data, cd_plot_curves, cd_outputfile_raw, cd_outputfile_capacities, state, cd_in_finishing
    if check_state(
            [States.Idle, States.Stationary_Graph]) and cd_getparams() and cd_validate_parameters() and validate_file(
        cd_parameters['filename']):
        cd_currentcycle = 1
        cd_charges = []
        cd_plot_curves = []
        cd_outputfile_raw = open(cd_parameters['filename'], 'w',
                                 1)  # This file will contain time, potential, and current data
        cd_outputfile_raw.write(
            f"""Device Serial:\t{dev.serial_number}
Lower Bound[V]:\t{cd_parameters['lbound']}
Upper Bound[V]:\t{cd_parameters['ubound']}
Charge Current[mA]:\t{cd_parameters['chargecurrent']}
Discharge Current[mA]:\t{cd_parameters['dischargecurrent']}
Half Cycles:\t{cd_parameters['numcycles']}
Samples to Average:\t{cd_parameters['numsamples']}

Elapsed_Time(s)\tPotential(V)\tCurrent(A)\tHalf-Cycle\n"""
        )
        # cd_outputfile_raw.write("Elapsed time(s)\tPotential(V)\tCurrent(A)\n")
        base, extension = os.path.splitext(cd_parameters['filename'])
        cd_outputfile_capacities = open(base + '_capacities' + extension, 'w',
                                        1)  # This file will contain capacity data for each cycle
        cd_outputfile_capacities.write("Cycle number\tCharge capacity (Ah)\tDischarge capacity (Ah)\n")
        cd_currentsetpoint = cd_parameters['chargecurrent']
        hardware_manual_control_range_dropdown.setCurrentIndex(current_range_from_current(
            cd_currentsetpoint))  # Determine the proper current range for the current setpoint
        set_current_range()  # Set new current range
        set_output(1, cd_currentsetpoint)  # Set current to setpoint
        set_control_mode(True)  # Galvanostatic control
        time.sleep(.2)  # Allow DAC some time to settle
        cd_starttime = timeit.default_timer()
        cd_time_data = AverageBuffer(cd_parameters['numsamples'])  # Holds averaged data for elapsed time
        cd_potential_data = AverageBuffer(cd_parameters['numsamples'])  # Holds averaged data for potential
        cd_current_data = AverageBuffer(cd_parameters['numsamples'])  # Holds averaged data for current
        set_cell_status(True)  # Cell on
        preview_cancel_button.hide()
        try:  # Set up the plotting area
            legend.scene().removeItem(legend)
        except AttributeError:
            pass
        plot_frame.clear()
        plot_frame.enableAutoRange()
        plot_frame.setLabel('bottom', 'Inserted/extracted charge', units="Ah")
        plot_frame.setLabel('left', 'Potential', units="V")
        cd_plot_curves.append(plot_frame.plot(pen=pen_color[0]))  # Draw potential as a function of charge in yellow
        log_message("Charge/discharge measurement started. Saving to: %s" % cd_parameters['filename'])
        cd_current_cycle_entry.setText("%d" % cd_currentcycle)  # Indicate the current cycle number
        state = States.Measuring_CD
        cd_in_finishing = False


def seq_cd_start():
    """Initialize the charge/discharge measurement."""
    global cd_charges, cd_currentsetpoint, cd_starttime, cd_currentcycle, cd_time_data, cd_potential_data, cd_current_data, cd_plot_curves, cd_outputfile_raw, cd_outputfile_capacities, state, cd_in_finishing
    # print("seq_cd_start")
    if check_state(
            [States.Idle, States.Stationary_Graph, States.Sequence_Idle]) and sequence_flag and cd_validate_parameters() and validate_file(
        cd_parameters['filename'], overwrite_protect=False):
        cd_currentcycle = 1
        cd_charges = []
        cd_plot_curves = []
        cd_outputfile_raw = open(cd_parameters['filename'], 'w',
                                 1)  # This file will contain time, potential, and current data
        cd_outputfile_raw.write(
            f"""Device Serial:\t{dev.serial_number}
Lower Bound[V]:\t{cd_parameters['lbound']}
Upper Bound[V]:\t{cd_parameters['ubound']}
Charge Current[mA]:\t{cd_parameters['chargecurrent']}
Discharge Current[mA]:\t{cd_parameters['dischargecurrent']}
Half Cycles:\t{cd_parameters['numcycles']}
Samples to Average:\t{cd_parameters['numsamples']}

Elapsed_Time(s)\tPotential(V)\tCurrent(A)\tHalf-Cycle\n"""
        )
        # cd_outputfile_raw.write("Elapsed time(s)\tPotential(V)\tCurrent(A)\n")
        base, extension = os.path.splitext(cd_parameters['filename'])
        cd_outputfile_capacities = open(base + '_capacities' + extension, 'w',
                                        1)  # This file will contain capacity data for each cycle
        cd_outputfile_capacities.write("Cycle number\tCharge capacity (Ah)\tDischarge capacity (Ah)\n")
        cd_currentsetpoint = cd_parameters['chargecurrent']
        hardware_manual_control_range_dropdown.setCurrentIndex(current_range_from_current(
            cd_currentsetpoint))  # Determine the proper current range for the current setpoint
        set_current_range()  # Set new current range
        set_output(1, cd_currentsetpoint)  # Set current to setpoint
        set_control_mode(True)  # Galvanostatic control
        time.sleep(.2)  # Allow DAC some time to settle
        cd_starttime = timeit.default_timer()
        cd_time_data = AverageBuffer(cd_parameters['numsamples'])  # Holds averaged data for elapsed time
        cd_potential_data = AverageBuffer(cd_parameters['numsamples'])  # Holds averaged data for potential
        cd_current_data = AverageBuffer(cd_parameters['numsamples'])  # Holds averaged data for current
        set_cell_status(True)  # Cell on
        preview_cancel_button.hide()
        try:  # Set up the plotting area
            legend.scene().removeItem(legend)
        except AttributeError:
            pass
        plot_frame.clear()
        plot_frame.enableAutoRange()
        plot_frame.setLabel('bottom', 'Inserted/extracted charge', units="Ah")
        plot_frame.setLabel('left', 'Potential', units="V")
        cd_plot_curves.append(plot_frame.plot(pen=pen_color[0]))  # Draw potential as a function of charge in yellow
        log_message("Charge/discharge measurement started. Saving to: %s" % cd_parameters['filename'])
        cd_current_cycle_entry.setText("%d" % cd_currentcycle)  # Indicate the current cycle number
        state = States.Measuring_CD
        cd_in_finishing = False
        # print("cd_start() completed")


def cd_update():
    """Add a new data point to the charge/discharge measurement (should be called regularly)."""
    global cd_currentsetpoint, cd_currentcycle, state, cd_in_finishing
    global current, settling_counter  # added while fixing cd_voltage_finish mode
    elapsed_time = timeit.default_timer() - cd_starttime
    if cd_currentcycle > cd_parameters['numcycles']:  # End of charge/discharge measurements
        cd_stop(interrupted=False)
    else:  # Continue charge/discharge measurement process
        read_potential_current()  # Read new potential and current
        cd_time_data.add_sample(elapsed_time)
        cd_potential_data.add_sample(potential)
        cd_current_data.add_sample(1e-3 * current)  # Convert mA to A
        if len(cd_time_data.samples) == 0 and len(cd_time_data.averagebuffer) > 0:  # A new average was just calculated
            # cd_outputfile_raw.write("%e\t%e\t%e\n" % (
            #     cd_time_data.averagebuffer[-1],
            #     cd_potential_data.averagebuffer[-1],
            #     cd_current_data.averagebuffer[-1]))  # Write it out
            cd_outputfile_raw.write(
                f"{cd_time_data.averagebuffer[-1]:e}\t"
                f"{cd_potential_data.averagebuffer[-1]:e}\t"
                f"{cd_current_data.averagebuffer[-1]:e}\t"
                f"{cd_currentcycle}\n"
            )
            charge = numpy.abs(scipy.integrate.cumtrapz(cd_current_data.averagebuffer, cd_time_data.averagebuffer,
                                                        initial=0.) / 3600.)  # Cumulative charge in Ah
            cd_plot_curves[cd_currentcycle - 1].setData(charge, cd_potential_data.averagebuffer)  # Update the graph
        if (cd_currentsetpoint > 0 and potential > cd_parameters['ubound']) or (cd_currentsetpoint < 0 and potential < cd_parameters['lbound']):  # A potential cut-off has been reached
#----------------------------------------------------------------------------------------------------------------------
            if cd_voltage_finish_flag == True:
                cd_in_finishing = True
            else:
                log_message("Cycle %s Finished" % cd_currentcycle)
                if cd_currentsetpoint == cd_parameters[
                    'chargecurrent']:  # Switch from the discharge phase to the charge phase or vice versa
                    cd_currentsetpoint = cd_parameters['dischargecurrent']
                else:
                    cd_currentsetpoint = cd_parameters['chargecurrent']
                hardware_manual_control_range_dropdown.setCurrentIndex(current_range_from_current(
                    cd_currentsetpoint))  # Determine the proper current range for the new setpoint
                set_current_range()  # Set new current range
                set_output(1, cd_currentsetpoint)  # Set current to setpoint
                cd_plot_curves.append(plot_frame.plot(
                    pen=pen_color[
                        cd_currentcycle % 10]))  # Start a new plot curve and append it to the plot area (keeping the old ones as well)
                cd_charges.append(numpy.abs(numpy.trapz(cd_current_data.averagebuffer,
                                                        cd_time_data.averagebuffer) / 3600.))  # Cumulative charge in Ah
                if cd_currentcycle % 2 == 0:  # Write out the charge and discharge capacities after both a charge and discharge phase (i.e. after cycle 2, 4, 6...)
                    cd_outputfile_capacities.write("%d\t%e\t%e\n" % (
                        cd_currentcycle / 2, cd_charges[cd_currentcycle - 2], cd_charges[cd_currentcycle - 1]))
                for data in [cd_time_data, cd_potential_data,
                             cd_current_data]:  # Clear average buffers to prepare them for the next cycle
                    data.clear()
                cd_currentcycle += 1  # Next cycle
                cd_current_cycle_entry.setText("%d" % cd_currentcycle)  # Indicate next cycle
    # ----------------------------------------------------------------------------------------------------------------------
        if cd_in_finishing == True:
            # ======================================================
            '''Sets time based ending parameter'''
            if cd_voltage_finish_time['semaphore'] == False and (cd_voltage_finish_mode == 0 or cd_voltage_finish_mode == 2):
                cd_voltage_finish_time['start_time'] = int(elapsed_time)
                # print(elapsed_time)
                cd_voltage_finish_time['end_time'] = elapsed_time + cd_parameters['finish_duration']
                log_message("Voltage finish duration: " + str(cd_parameters['finish_duration']))
                cd_voltage_finish_time['semaphore'] = True  # write-lock the flag
            # ======================================================
            if cd_voltage_finish_current['semaphore'] == False and (cd_voltage_finish_mode == 1 or cd_voltage_finish_mode == 2):
                '''Sets current based ending parameter'''
                # actual_current = numpy.abs(numpy.trapz(cd_current_data.averagebuffer, cd_time_data.averagebuffer) / 3600.)
                # cd_voltage_finish_current['start_current'] = actual_current
                # cd_voltage_finish_current['end_current'] = actual_current + cd_parameters['current_duration'] * 1e-6

                '''If in an odd numbered half-cycle, select end limit based on charge entry, if in an even numbered half-cycle, select end limit based on discharge entry'''
                if cd_currentcycle % 2 == 1:
                    # print(f"setting end current to {cd_parameters['chargecurrent_duration']}")
                    log_message("Voltage finish current: " + str(cd_parameters['chargecurrent_duration']))
                    cd_voltage_finish_current['end_current'] = cd_parameters['chargecurrent_duration']
                elif cd_currentcycle % 2 == 0:
                    # print(f"setting end current to {cd_parameters['dischargecurrent_duration']}")
                    log_message("Voltage finish current: " + str(cd_parameters['dischargecurrent_duration']))
                    cd_voltage_finish_current['end_current'] = cd_parameters['dischargecurrent_duration']
                cd_voltage_finish_current['semaphore'] = True  # write-lock the flag
            # ======================================================
            if control_mode == "GALVANOSTATIC":
                set_control_mode(False)  # Switch to potentiostatic control
            # ======================================================
            compensation_offset = 0.0003  # Offset needed to compensate for switching modes
            if cd_currentsetpoint > 0:
                # maintained_voltage = cd_parameters['ubound'] + 0.0005  # Sets the Constant Voltage to the upper bound, offset needed to compensate for switching modes
                # print("maintained voltage ubound")
                maintained_voltage = cd_parameters['ubound'] + compensation_offset
            # ======================================================
            elif cd_currentsetpoint < 0:
                # maintained_voltage = cd_parameters['lbound'] + 0.0005  # Sets the Constant Voltage to the lower bound, offset needed to compensate for switching modes
                # print("maintained voltage lbound")
                maintained_voltage = cd_parameters['lbound'] + compensation_offset
            else:
                print("Error: maintained voltage 0")
                maintained_voltage = 0
            # ======================================================
            if cd_voltage_finish_mode == 0:  # Voltage finish is time mode
                if cd_voltage_finish_time['end_time'] > elapsed_time:  # Time has elapsed
                    """Output data to the DAC; units can be either V (index 0), mA (index 1), or raw counts (index 2)."""
                    set_output(0, maintained_voltage)
                if elapsed_time > cd_voltage_finish_time['end_time']:  # Time has elapsed
                    cd_voltage_finish_time['semaphore'] = False  # Release the write-lock on the flag
                    cd_in_finishing = False
                    log_message("Cycle %s finished" % cd_currentcycle)
                    if cd_currentsetpoint == cd_parameters[
                        'chargecurrent']:  # Switch from the discharge phase to the charge phase or vice versa
                        cd_currentsetpoint = cd_parameters['dischargecurrent']
                    else:
                        cd_currentsetpoint = cd_parameters['chargecurrent']
                    if control_mode == "POTENTIOSTATIC":
                        set_control_mode(True)  # Switch to galvanostatic control
                    hardware_manual_control_range_dropdown.setCurrentIndex(current_range_from_current(
                        cd_currentsetpoint))  # Determine the proper current range for the new setpoint
                    set_current_range()  # Set new current range
                    set_output(1, cd_currentsetpoint)  # Set current to setpoint
                    cd_charges.append(numpy.abs(numpy.trapz(cd_current_data.averagebuffer,
                                                            cd_time_data.averagebuffer) / 3600.))  # Cumulative charge in Ah
                    if cd_currentcycle % 2 == 0:  # Write out the charge and discharge capacities after both a charge and discharge phase (i.e. after cycle 2, 4, 6...)
                        cd_outputfile_capacities.write("%d\t%e\t%e\n" % (
                            cd_currentcycle / 2, cd_charges[cd_currentcycle - 2], cd_charges[cd_currentcycle - 1]))
                    for data in [cd_time_data, cd_potential_data,
                                 cd_current_data]:  # Clear average buffers to prepare them for the next cycle
                        data.clear()
                    cd_currentcycle += 1  # Next cycle
                    cd_current_cycle_entry.setText("%d" % cd_currentcycle)  # Indicate next cycle
                    cd_plot_curves.append(plot_frame.plot(pen=pen_color[(cd_currentcycle-1) % 10]))  # Start a new plot curve and append it to the plot area  pen=pen_color[cd_currentcycle % len(pen_color)]
            # ======================================================
            elif cd_voltage_finish_mode == 1:  # Voltage finish is current mode
                # actual_current = numpy.abs(numpy.trapz(cd_current_data.averagebuffer, cd_time_data.averagebuffer) / 3600.)
                # if cd_voltage_finish_current['end_current'] > actual_current:  # Time has elapsed
                #     """Output data to the DAC; units can be either V (index 0), mA (index 1), or raw counts (index 2)."""
                #     set_output(0, maintained_voltage)
                # actual_current = numpy.abs(
                #     numpy.trapz(cd_current_data.averagebuffer, cd_time_data.averagebuffer) / 3600.)
                # if cd_voltage_finish_current['end_current'] < current:
                #     """Output data to the DAC; units can be either V (index 0), mA (index 1), or raw counts (index 2)."""
                #     set_output(0, maintained_voltage)
                # if current > cd_voltage_finish_current['end_current'] and maintained_voltage == cd_parameters['ubound']:
                #     """Output data to the DAC; units can be either V (index 0), mA (index 1), or raw counts (index 2)."""
                #     set_output(0, maintained_voltage)
                #     print(f"mode 1, setting output to ubound, current: {current}, end_current: {cd_voltage_finish_current['end_current']}")
                # elif current < cd_voltage_finish_current['end_current'] and maintained_voltage == cd_parameters['lbound']:
                #     """Output data to the DAC; units can be either V (index 0), mA (index 1), or raw counts (index 2)."""
                #     set_output(0, maintained_voltage)
                #     print(f"mode 1, setting output to lbound, current: {current}, end_current: {cd_voltage_finish_current['end_current']}")
                if (current < cd_voltage_finish_current['end_current']
                      and maintained_voltage == cd_parameters['ubound']+0.0003) \
                        or (current > cd_voltage_finish_current['end_current']
                            and maintained_voltage == cd_parameters['lbound']+0.0003):  # Time has elapsed
                    settling_counter -= 1
                    # print(f"Settling counter: {settling_counter}")
                    if settling_counter == 0:
                        # print(f"mode 1, ending cycle. Current: {current}, end_current: {cd_voltage_finish_current['end_current']}, maintained_voltage: {maintained_voltage}")
                        cd_voltage_finish_current['semaphore'] = False  # Release the write-lock on the flag
                        cd_in_finishing = False
                        log_message("Cycle %s finished" % cd_currentcycle)
                        if cd_currentsetpoint == cd_parameters[
                            'chargecurrent']:  # Switch from the discharge phase to the charge phase or vice versa
                            cd_currentsetpoint = cd_parameters['dischargecurrent']
                        else:
                            cd_currentsetpoint = cd_parameters['chargecurrent']
                        if control_mode == "POTENTIOSTATIC":
                            set_control_mode(True)  # Switch to galvanostatic control
                        hardware_manual_control_range_dropdown.setCurrentIndex(current_range_from_current(
                            cd_currentsetpoint))  # Determine the proper current range for the new setpoint
                        set_current_range()  # Set new current range
                        set_output(1, cd_currentsetpoint)  # Set current to setpoint
                        cd_charges.append(numpy.abs(numpy.trapz(cd_current_data.averagebuffer,
                                                                cd_time_data.averagebuffer) / 3600.))  # Cumulative charge in Ah
                        if cd_currentcycle % 2 == 0:  # Write out the charge and discharge capacities after both a charge and discharge phase (i.e. after cycle 2, 4, 6...)
                            cd_outputfile_capacities.write("%d\t%e\t%e\n" % (
                                cd_currentcycle / 2, cd_charges[cd_currentcycle - 2], cd_charges[cd_currentcycle - 1]))
                        for data in [cd_time_data, cd_potential_data,
                                     cd_current_data]:  # Clear average buffers to prepare them for the next cycle
                            data.clear()
                        cd_currentcycle += 1  # Next cycle
                        cd_current_cycle_entry.setText("%d" % cd_currentcycle)  # Indicate next cycle
                        cd_plot_curves.append(plot_frame.plot(pen=pen_color[(
                                                                                        cd_currentcycle - 1) % 10]))  # Start a new plot curve and append it to the plot area  pen=pen_color[cd_currentcycle % len(pen_color)]
                        settling_counter = 3
                else:
                    set_output(0, maintained_voltage)
                    # print(f"mode 1, setting maintained voltage output, current: {current}, end_current: {cd_voltage_finish_current['end_current']}")

            # ======================================================
            elif cd_voltage_finish_mode == 2:  # Voltage finish is both time and current mode
                # if control_mode == "GALVANOSTATIC":
                #     set_control_mode(False)  # Switch to potentiostatic control
                # actual_current = numpy.abs(
                #     numpy.trapz(cd_current_data.averagebuffer, cd_time_data.averagebuffer) / 3600.)
                # if (cd_voltage_finish_current['end_current'] > actual_current) or (cd_voltage_finish_time['end_time'] > elapsed_time):  # Time has elapsed
                #     """Output data to the DAC; units can be either V (index 0), mA (index 1), or raw counts (index 2)."""
                #     set_output(0, maintained_voltage)
                if (current > cd_voltage_finish_current['end_current'] and maintained_voltage == cd_parameters['ubound'] + compensation_offset) \
                        and (cd_voltage_finish_time['end_time'] > elapsed_time):
                    """Output data to the DAC; units can be either V (index 0), mA (index 1), or raw counts (index 2)."""
                    set_output(0, maintained_voltage)
                elif (current < cd_voltage_finish_current['end_current'] and maintained_voltage == cd_parameters['lbound'] + compensation_offset) \
                        and (cd_voltage_finish_time['end_time'] > elapsed_time):
                    """Output data to the DAC; units can be either V (index 0), mA (index 1), or raw counts (index 2)."""
                    set_output(0, maintained_voltage)
                elif (current < cd_voltage_finish_current['end_current']
                      and maintained_voltage == cd_parameters['ubound']) \
                        or (current > cd_voltage_finish_current['end_current']
                            and maintained_voltage == cd_parameters['lbound']) \
                        or (elapsed_time > cd_voltage_finish_time['end_time']):  # Time has elapsed
                    if (elapsed_time > cd_voltage_finish_time['end_time']):
                        log_message("Voltage finish end due to time settings")
                    else:
                        log_message("Voltage finish end due to current settings")
                    cd_voltage_finish_current['semaphore'] = False  # Release the write-lock on the flag
                    cd_voltage_finish_time['semaphore'] = False  # Release the write-lock on the flag
                    cd_in_finishing = False
                    log_message("Cycle %s finished" % cd_currentcycle)
                    if cd_currentsetpoint == cd_parameters[
                        'chargecurrent']:  # Switch from the discharge phase to the charge phase or vice versa
                        cd_currentsetpoint = cd_parameters['dischargecurrent']
                    else:
                        cd_currentsetpoint = cd_parameters['chargecurrent']
                    if control_mode == "POTENTIOSTATIC":
                        set_control_mode(True)  # Switch to galvanostatic control
                    hardware_manual_control_range_dropdown.setCurrentIndex(current_range_from_current(
                        cd_currentsetpoint))  # Determine the proper current range for the new setpoint
                    set_current_range()  # Set new current range
                    set_output(1, cd_currentsetpoint)  # Set current to setpoint
                    cd_charges.append(numpy.abs(numpy.trapz(cd_current_data.averagebuffer,
                                                            cd_time_data.averagebuffer) / 3600.))  # Cumulative charge in Ah
                    if cd_currentcycle % 2 == 0:  # Write out the charge and discharge capacities after both a charge and discharge phase (i.e. after cycle 2, 4, 6...)
                        cd_outputfile_capacities.write("%d\t%e\t%e\n" % (
                            cd_currentcycle / 2, cd_charges[cd_currentcycle - 2], cd_charges[cd_currentcycle - 1]))
                    for data in [cd_time_data, cd_potential_data,
                                 cd_current_data]:  # Clear average buffers to prepare them for the next cycle
                        data.clear()
                    cd_currentcycle += 1  # Next cycle
                    cd_current_cycle_entry.setText("%d" % cd_currentcycle)  # Indicate next cycle
                    cd_plot_curves.append(plot_frame.plot(pen=pen_color[(
                                                                                cd_currentcycle - 1) % 10]))  # Start a new plot curve and append it to the plot area  pen=pen_color[cd_currentcycle % len(pen_color)]

            # ----------------------------------------------------------------------------------------------------------------------

def cd_stop(interrupted=True):
    """Finish the charge/discharge measurement."""
    global state, sequence_index
    sequence_index += 1
    if check_state([States.Measuring_CD]):
        set_cell_status(False)  # Cell off
        cd_outputfile_raw.close()
        cd_outputfile_capacities.close()
        if interrupted:
            log_message("Charge/discharge measurement interrupted. Calculated charges (in uAh): [" + ', '.join(
                "%.2f" % (value * 1e6) for value in
                cd_charges) + "]")  # Print list of inserted/extracted charges to the message log
        else:
            log_message("Charge/discharge measurement finished. Calculated charges (in uAh): [" + ', '.join(
                "%.2f" % (value * 1e6) for value in
                cd_charges) + "]")  # Print list of inserted/extracted charges to the message log
        cd_current_cycle_entry.setText("")  # Clear cycle indicator
        if sequence_flag == False:
            state = States.Stationary_Graph  # Keep displaying the last plot until the user clicks a button
            preview_cancel_button.show()
        if sequence_flag == True:
            state = States.Sequence_Idle
        GraphAutoExport(plot_frame, cd_parameters['filename'])


def rate_getparams():
    """Retrieve the rate testing parameters from the GUI input fields and store them in a global dictionary. If succesful, return True."""
    global rate_parameters
    try:
        rate_parameters['lbound'] = float(rate_lbound_entry.text())
        rate_parameters['ubound'] = float(rate_ubound_entry.text())
        rate_parameters['one_c_current'] = float(rate_capacity_entry.text()) / 1e3  # Convert uA to mA
        rate_parameters['crates'] = [float(x) for x in rate_crates_entry.text().split(",")]
        rate_parameters['currents'] = [rate_parameters['one_c_current'] * rc for rc in rate_parameters['crates']]
        rate_parameters['numcycles'] = int(rate_numcycles_entry.text())
        # rate_parameters['numsamples'] = int(rate_numsamples_entry.text())
        rate_parameters['filename'] = str(rate_file_entry.text())
        return True
    except ValueError:
        QtWidgets.QMessageBox.critical(mainwidget, "Not a number",
                                   "One or more parameters could not be interpreted as a number.")
        return False


def rate_validate_parameters():
    """Check if the chosen charge/discharge parameters make sense. If so, return True."""
    if rate_parameters['ubound'] < rate_parameters['lbound']:
        QtWidgets.QMessageBox.critical(mainwidget, "Rate testing error",
                                   "The upper bound cannot be lower than the lower bound.")
        return False
    if 0. in rate_parameters['currents']:
        QtWidgets.QMessageBox.critical(mainwidget, "Rate testing error", "The charge/discharge current cannot be zero.")
        return False
    if rate_parameters['numcycles'] <= 0:
        QtWidgets.QMessageBox.critical(mainwidget, "Charge/discharge error",
                                   "The number of half cycles must be positive and non-zero.")
        return False
    return True


def rate_start():
    """Initialize the rate testing measurement."""
    global state, crate_index, rate_halfcycle_countdown, rate_chg_charges, rate_dis_charges, rate_outputfile_raw, rate_outputfile_capacities, rate_starttime, rate_time_data, rate_potential_data, rate_current_data, rate_plot_scatter_chg, rate_plot_scatter_dis, legend
    if check_state([States.Idle,
                    States.Stationary_Graph]) and rate_getparams() and rate_validate_parameters() and validate_file(
        rate_parameters['filename']):
        crate_index = 0  # Index in the list of C-rates
        rate_halfcycle_countdown = 2 * rate_parameters['numcycles']  # Holds amount of remaining half cycles
        rate_chg_charges = []  # List of measured charge capacities
        rate_dis_charges = []  # List of measured discharge capacities
        rate_outputfile_raw = open(rate_parameters['filename'], 'w',
                                   1)  # This file will contain time, potential, and current data
        rate_outputfile_raw.write("Elapsed time(s)\tPotential(V)\tCurrent(A)\n")
        base, extension = os.path.splitext(rate_parameters['filename'])
        rate_outputfile_capacities = open(base + '_capacities' + extension, 'w',
                                          1)  # This file will contain capacity data for each C-rate
        rate_outputfile_capacities.write("C-rate\tCharge capacity (Ah)\tDischarge capacity (Ah)\n")
        rate_current = rate_parameters['currents'][crate_index] if rate_halfcycle_countdown % 2 == 0 else - \
            rate_parameters['currents'][
                crate_index]  # Apply positive current for odd half cycles (charge phase) and negative current for even half cycles (discharge phase)
        hardware_manual_control_range_dropdown.setCurrentIndex(
            current_range_from_current(rate_current))  # Determine the proper current range for the current setpoint
        set_current_range()  # Set new current range
        set_output(1, rate_current)  # Set current to setpoint
        set_control_mode(True)  # Galvanostatic control
        time.sleep(.2)  # Allow DAC some time to settle
        rate_starttime = timeit.default_timer()
        numsamples = max(1, int(36. / rate_parameters['crates'][crate_index]))
        rate_time_data = AverageBuffer(numsamples)  # Holds averaged data for elapsed time
        rate_potential_data = AverageBuffer(numsamples)  # Holds averaged data for potential
        rate_current_data = AverageBuffer(numsamples)  # Holds averaged data for current
        set_cell_status(True)  # Cell on
        preview_cancel_button.hide()
        try:  # Set up the plotting area
            legend.scene().removeItem(legend)
        except AttributeError:
            pass
        plot_frame.clear()
        legend = plot_frame.addLegend()
        plot_frame.enableAutoRange()
        plot_frame.setLabel('bottom', 'C-rate')
        plot_frame.setLabel('left', 'Inserted/extracted charge', units="Ah")
        rate_plot_scatter_chg = plot_frame.plot(symbol='o', pen=None, symbolPen='r', symbolBrush='r',
                                                name='Charge')  # Plot charge capacity as a function of C-rate with red circles
        rate_plot_scatter_dis = plot_frame.plot(symbol='o', pen=None, symbolPen=(100, 100, 255),
                                                symbolBrush=(100, 100, 255),
                                                name='Discharge')  # Plot discharge capacity as a function of C-rate with blue circles
        log_message("Rate testing started. Saving to: %s" % rate_parameters['filename'])
        rate_current_crate_entry.setText("%d" % rate_parameters['crates'][crate_index])  # Indicate the current C-rate
        state = States.Measuring_Rate


def seq_rate_start():
    """Initialize the rate testing measurement."""
    global state, crate_index, rate_halfcycle_countdown, rate_chg_charges, rate_dis_charges, rate_outputfile_raw, rate_outputfile_capacities, rate_starttime, rate_time_data, rate_potential_data, rate_current_data, rate_plot_scatter_chg, rate_plot_scatter_dis, legend
    # print("seq_rate_start")
    if check_state([States.Idle, States.Stationary_Graph, States.Sequence_Idle]) and sequence_flag and rate_validate_parameters() and validate_file(
        rate_parameters['filename'], overwrite_protect=False):
        crate_index = 0  # Index in the list of C-rates
        rate_halfcycle_countdown = 2 * rate_parameters['numcycles']  # Holds amount of remaining half cycles
        rate_chg_charges = []  # List of measured charge capacities
        rate_dis_charges = []  # List of measured discharge capacities
        rate_outputfile_raw = open(rate_parameters['filename'], 'w',
                                   1)  # This file will contain time, potential, and current data
        rate_outputfile_raw.write("Elapsed time(s)\tPotential(V)\tCurrent(A)\n")
        base, extension = os.path.splitext(rate_parameters['filename'])
        rate_outputfile_capacities = open(base + '_capacities' + extension, 'w',
                                          1)  # This file will contain capacity data for each C-rate
        rate_outputfile_capacities.write("C-rate\tCharge capacity (Ah)\tDischarge capacity (Ah)\n")
        rate_current = rate_parameters['currents'][crate_index] if rate_halfcycle_countdown % 2 == 0 else - \
            rate_parameters['currents'][
                crate_index]  # Apply positive current for odd half cycles (charge phase) and negative current for even half cycles (discharge phase)
        hardware_manual_control_range_dropdown.setCurrentIndex(
            current_range_from_current(rate_current))  # Determine the proper current range for the current setpoint
        set_current_range()  # Set new current range
        set_output(1, rate_current)  # Set current to setpoint
        set_control_mode(True)  # Galvanostatic control
        time.sleep(.2)  # Allow DAC some time to settle
        rate_starttime = timeit.default_timer()
        numsamples = max(1, int(36. / rate_parameters['crates'][crate_index]))
        rate_time_data = AverageBuffer(numsamples)  # Holds averaged data for elapsed time
        rate_potential_data = AverageBuffer(numsamples)  # Holds averaged data for potential
        rate_current_data = AverageBuffer(numsamples)  # Holds averaged data for current
        set_cell_status(True)  # Cell on
        preview_cancel_button.hide()
        try:  # Set up the plotting area
            legend.scene().removeItem(legend)
        except AttributeError:
            pass
        plot_frame.clear()
        legend = plot_frame.addLegend()
        plot_frame.enableAutoRange()
        plot_frame.setLabel('bottom', 'C-rate')
        plot_frame.setLabel('left', 'Inserted/extracted charge', units="Ah")
        rate_plot_scatter_chg = plot_frame.plot(symbol='o', pen=None, symbolPen='r', symbolBrush='r',
                                                name='Charge')  # Plot charge capacity as a function of C-rate with red circles
        rate_plot_scatter_dis = plot_frame.plot(symbol='o', pen=None, symbolPen=(100, 100, 255),
                                                symbolBrush=(100, 100, 255),
                                                name='Discharge')  # Plot discharge capacity as a function of C-rate with blue circles
        log_message("Rate testing started. Saving to: %s" % rate_parameters['filename'])
        rate_current_crate_entry.setText("%d" % rate_parameters['crates'][crate_index])  # Indicate the current C-rate
        state = States.Measuring_Rate


def rate_update():
    # print("rate_update")
    """Add a new data point to the rate testing measurement (should be called regularly)."""
    global state, crate_index, rate_halfcycle_countdown
    elapsed_time = timeit.default_timer() - rate_starttime
    read_potential_current()
    rate_time_data.add_sample(elapsed_time)
    rate_potential_data.add_sample(potential)
    rate_current_data.add_sample(1e-3 * current)  # Convert mA to A
    if len(rate_time_data.samples) == 0 and len(rate_time_data.averagebuffer) > 0:  # A new average was just calculated
        rate_outputfile_raw.write("%e\t%e\t%e\n" % (
            rate_time_data.averagebuffer[-1], rate_potential_data.averagebuffer[-1],
            rate_current_data.averagebuffer[-1]))  # Write it out
    if (rate_halfcycle_countdown % 2 == 0 and potential > rate_parameters['ubound']) or (
            rate_halfcycle_countdown % 2 != 0 and potential < rate_parameters[
        'lbound']):  # A potential cut-off has been reached
        rate_halfcycle_countdown -= 1
        if rate_halfcycle_countdown == 1:  # Last charge cycle for this C-rate, so calculate and plot the charge capacity
            charge = numpy.abs(scipy.integrate.trapz(rate_current_data.averagebuffer,
                                                     rate_time_data.averagebuffer) / 3600.)  # Charge in Ah
            rate_chg_charges.append(charge)
            rate_plot_scatter_chg.setData(rate_parameters['crates'][0:crate_index + 1], rate_chg_charges)
        elif rate_halfcycle_countdown == 0:  # Last discharge cycle for this C-rate, so calculate and plot the discharge capacity, and go to the next C-rate
            charge = numpy.abs(scipy.integrate.trapz(rate_current_data.averagebuffer,
                                                     rate_time_data.averagebuffer) / 3600.)  # Charge in Ah
            rate_dis_charges.append(charge)
            rate_plot_scatter_dis.setData(rate_parameters['crates'][0:crate_index + 1], rate_dis_charges)
            rate_outputfile_capacities.write(
                "%e\t%e\t%e\n" % (rate_parameters['crates'][crate_index], rate_chg_charges[-1], rate_dis_charges[-1]))
            if crate_index == len(rate_parameters['crates']) - 1:  # Last C-rate was measured
                rate_stop(interrupted=False)
                return
            else:  # New C-rate
                crate_index += 1
                rate_halfcycle_countdown = 2 * rate_parameters[
                    'numcycles']  # Set the amount of remaining half cycles for the new C-rate
                set_output(1, 0.)  # Set zero current while range switching
                hardware_manual_control_range_dropdown.setCurrentIndex(current_range_from_current(
                    rate_parameters['currents'][
                        crate_index]))  # Determine the proper current range for the new setpoint
                set_current_range()  # Set new current range
                numsamples = max(1, int(36. / rate_parameters['crates'][
                    crate_index]))  # Set an appropriate amount of samples to average for the new C-rate; results in approx. 1000 points per curve
                for data in [rate_time_data, rate_potential_data, rate_current_data]:
                    data.number_of_samples_to_average = numsamples
        rate_current = rate_parameters['currents'][crate_index] if rate_halfcycle_countdown % 2 == 0 else - \
            rate_parameters['currents'][
                crate_index]  # Apply positive current for odd half cycles (charge phase) and negative current for even half cycles (discharge phase)
        set_output(1, rate_current)  # Set current to setpoint
        for data in [rate_time_data, rate_potential_data,
                     rate_current_data]:  # Clear average buffers to prepare them for the next cycle
            data.clear()
        rate_current_crate_entry.setText("%d" % rate_parameters['crates'][crate_index])  # Indicate the next C-rate


def rate_stop(interrupted=True):
    """Finish the rate testing measurement."""
    global state, sequence_index
    sequence_index += 1
    if check_state([States.Measuring_Rate]):
        state = States.Idle_Init
        set_cell_status(False)  # Cell off
        rate_outputfile_raw.close()
        rate_outputfile_capacities.close()
        if interrupted:
            log_message("Rate testing interrupted.")
        else:
            log_message("Rate testing finished.")
        rate_current_crate_entry.setText("")  # Clear C-rate indicator
        if sequence_flag == False:
            state = States.Stationary_Graph  # Keep displaying the last plot until the user clicks a button
            preview_cancel_button.show()
        if sequence_flag == True:
            state = States.Sequence_Idle
        GraphAutoExport(plot_frame, rate_parameters['filename'])


def plotinterval_changed():
    if plotinterval_combobox.currentText() == "Custom":
        plotinterval_custom_entry.setEnabled(True)
    else:
        plotinterval_custom_entry.setEnabled(False)

def temp_getparams():
    global temp_parameters, temp_sensor_type
    try:
        days = int(temp_duration_days.text())
        hours = int(temp_duration_hours.text())
        minutes = int(temp_duration_minutes.text())
        seconds = int(temp_duration_seconds.text())
        temp_parameters['duration'] = days * 86400 + hours * 3600 + minutes * 60 + seconds
        if temp_pt1000_radio_entry.isChecked():
            temp_sensor_type = True
            temp_parameters["sensor_type"] = True
        elif temp_pt100_radio_entry.isChecked():
            temp_sensor_type = False
            temp_parameters["sensor_type"] = False
        plotIntervalIndex = plotinterval_combobox.currentIndex()
        plotIntervalList = [1, 5, 15, 30, 60, 300, 600, 900, 1800, 3600, "Custom"]
        if plotIntervalList[plotIntervalIndex] == "Custom":
            plotinterval = int(plotinterval_custom_entry.text())
        else:
            plotinterval = plotIntervalList[plotIntervalIndex]
        temp_parameters['plotinterval'] = plotinterval
        temp_parameters['filename'] = str(temp_file_entry.text())
        # temp_parameters['target_temperature'] = float(target_temp_entry.text())
        # temp_parameters['stable_duration'] = int(target_temp_stableduration_entry.text())
        return True
    except ValueError:
        QtWidgets.QMessageBox.critical(mainwidget, "Not a number",
                                   "One or more parameters could not be interpreted as a number.")
        return False


def temp_validate_parameters():
    """Check if the chosen charge/discharge parameters make sense. If so, return True."""
    if temp_parameters['duration'] <= 0:
        QtWidgets.QMessageBox.critical(mainwidget, "Duration Error",
                                   "Duration cannot be negative or zero.")
        return False
    if temp_parameters['plotinterval'] <= 0:
        QtWidgets.QMessageBox.critical(mainwidget, "Plot Interval Error", "The plot interval cannot be negative or zero.")
        return False
    return True


def start_temp_measurement():
    global state, temp_plot_curves, temp_outputfile_raw, temp_sensor_type, temp_starttime, temp_time_data, temp_potential_data, temp_current_data, temp_temperature_data, temp_parameters
    if check_state([States.Idle,
                    States.Stationary_Graph]) and temp_getparams() and temp_validate_parameters() and validate_file(
        temp_parameters['filename']):
        temp_plot_curves = []
        if temp_sensor_type:
            sensor = "PT1000"
        elif not temp_sensor_type:
            sensor = "PT100"
        test_start = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        test_end = datetime.datetime.now() + datetime.timedelta(
            seconds=temp_parameters['duration'])
        test_end_text = test_end.strftime("%Y-%m-%d %H:%M:%S")
        temp_outputfile_raw = open(temp_parameters['filename'], 'w', 1)  # 1 means line-buffered
        temp_outputfile_raw.write(
            f"""Device Serial:\t{dev.serial_number}
Start Time:\t{test_start}
Estimated End Time:\t{test_end_text}
Duration (s):\t{temp_parameters['duration']}
Plot Interval (s):\t{temp_parameters['plotinterval']}
Sensor Type:\t{sensor}

Elapsed_Time\tPotential(V)\tCurrent(A)\tTemperature(Deg C)\n""")
        set_output(1, 1)  # first part is mode 1 (mA), second part is current value of 1 mA
        set_control_mode(True)  # Galvanostatic control
        time.sleep(.2)  # Allow DAC some time to settle
        temp_starttime = timeit.default_timer()
        samplesToAverage = int(int(temp_parameters['plotinterval'])*11.11111111111111)
        temp_time_data = AverageBuffer(samplesToAverage)  # Holds averaged data for elapsed time
        temp_potential_data = AverageBuffer(samplesToAverage)  # Holds averaged data for potential
        temp_current_data = AverageBuffer(samplesToAverage)  # Holds averaged data for current
        temp_temperature_data = AverageBuffer(samplesToAverage)
        set_cell_status(True)  # Cell on
        preview_cancel_button.hide()
        try:  # Set up the plotting area
            legend.scene().removeItem(legend)
        except AttributeError:
            pass
        plot_frame.clear()
        plot_frame.enableAutoRange()
        plot_frame.setLabel('bottom', 'Time', units="s")
        plot_frame.setLabel('left', 'Temperature', units="\u2103")
        temp_plot_curves.append(plot_frame.plot(pen=pen_color[0]))  # Draw potential as a function of charge in yellow
        log_message("Temperature measurement started. Saving to: %s" % temp_parameters['filename'])
        state = States.Measuring_Temp


def update_temp_measurement():
    global state, temp_outputfile_raw, temp_sensor_type, temp_starttime, temp_time_data, temp_potential_data, temp_current_data, temp_temperature_data, temp_parameters, temp_sensor_type
    elapsed_time = timeit.default_timer() - temp_starttime
    if elapsed_time >= temp_parameters['duration']:
        stop_temp_measurement(interrupted=False)
    else:
        read_potential_current()
        temp_time_data.add_sample(elapsed_time)
        temp_potential_data.add_sample(potential)
        temp_current_data.add_sample(current * 1e-3)  # Convert mA to A
        if temp_sensor_type:
            RTD_res = 1000
            RperDeg = 3.85
        elif not temp_sensor_type:
            RTD_res = 100
            RperDeg = 0.385
        temp_temperature_data.add_sample(((potential/(current*1e-3))-RTD_res)/RperDeg)
        if len(temp_time_data.samples) == 0 and len(temp_time_data.averagebuffer) > 0:  # A new average was just calculated
            temp_outputfile_raw.write(
                f"{temp_time_data.averagebuffer[-1]:e}\t"
                f"{temp_potential_data.averagebuffer[-1]:e}\t"
                f"{temp_current_data.averagebuffer[-1]:e}\t"
                f"{temp_temperature_data.averagebuffer[-1]:e}\n"
            )
            temp_plot_curves[0].setData(temp_time_data.averagebuffer, temp_temperature_data.averagebuffer)
            # temp_out = (temp_temperature_data.averagebuffer[-1]:.2f)
            temperature_monitor.setText(f"{temp_temperature_data.averagebuffer[-1]:.2f} \u2103")


def stop_temp_measurement(interrupted=True):
    global state
    if check_state([States.Measuring_Temp]):
        set_cell_status(False)  # Cell off
        temp_outputfile_raw.close()
        if interrupted:
            log_message("Temperature measurement interrupted.")
        else:
            log_message("Temperature measurement finished.")
        state = States.Stationary_Graph
        preview_cancel_button.show()
        GraphAutoExport(plot_frame, temp_parameters['filename'])


def ocp_getparams():
    global ocp_parameters
    try:
        ocp_parameters['duration'] = int(ocp_duration_entry.text())
        ocp_parameters['numsamples'] = int(ocp_numsamples_entry.text())
        ocp_parameters['filename'] = str(ocp_file_entry.text())
        return True
    except ValueError:
        QtWidgets.QMessageBox.critical(mainwidget, "Not a number",
                                   "One or more parameters could not be interpreted as a number.")
        return False


def ocp_validate_parameters():
    if ocp_parameters['duration'] <= 0:
        QtWidgets.QMessageBox.critical(mainwidget, "Duration too short",
                                   "The duration must be at least 1 second.")
        return False
    if ocp_parameters['numsamples'] <= 0:
        QtWidgets.QMessageBox.critical(mainwidget, "Number of samples too small",
                                   "The number of samples must be at least 1.")
        return False
    return True


def ocp_start():
    global state, ocp_outputfile, ocp_plot_curve, ocp_time_data, ocp_potential_data, potential_buffer
    if check_state([States.Idle, States.Stationary_Graph]) and ocp_getparams() and ocp_validate_parameters() and validate_file(ocp_parameters['filename']):
        ocp_starttime_text = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        ocp_endtime = datetime.datetime.now() + datetime.timedelta(seconds=ocp_parameters['duration'])
        ocp_end_text = ocp_endtime.strftime("%Y-%m-%d %H:%M:%S")
        ocp_outputfile = open(ocp_parameters['filename'], 'w', 1)  # 1 means line-buffered
        # do not change spacing below - it will change the fileheader
        ocp_outputfile.write(
            f"""Device Serial:\t{dev.serial_number}\nDuration[s]:\t{ocp_parameters['duration']}
            Start Time:\t{ocp_starttime_text}\nEstimated End:\t{ocp_end_text}
            Samples to Average:\t{ocp_parameters['numsamples']}\nElapsed_Time(s)\tPotential(V)\n"""
        )
        ocp_time_data = AverageBuffer(ocp_parameters['numsamples'])
        ocp_potential_data = AverageBuffer(ocp_parameters['numsamples'])
        potential_buffer = AverageBuffer(ocp_parameters['numsamples'])
        time.sleep(.1)  # Allow feedback loop some time to settle
        read_potential_current()
        time.sleep(.1)
        read_potential_current()  # Two reads are necessary because each read actually returns the result of the previous conversion

        preview_cancel_button.hide()
        try:  # Set up the plotting area
            legend.scene().removeItem(legend)
        except AttributeError:
            pass
        plot_frame.clear()
        plot_frame.enableAutoRange()
        # plot_frame.setXRange(0, 30, update=True)
        plot_frame.setLabel('bottom', 'Time', units="S")
        plot_frame.setLabel('left', 'Voltage', units="V")
        ocp_plot_curve = plot_frame.plot(pen=pen_color[0])  # Plot first cycle CV in yellow, changes with cycle number
        log_message("OCP measurement started. Saving to: %s" % ocp_parameters['filename'])
        state = States.Measuring_OCP
        ocp_parameters['starttime'] = timeit.default_timer()


def ocp_update():
    global statel, potential_buffer
    elapsed_time = timeit.default_timer() - ocp_parameters['starttime']
    if elapsed_time > ocp_parameters['duration']:
        ocp_stop(interrupted=False)
    else:
        read_potential_current()
        ocp_time_data.add_sample(elapsed_time)
        ocp_potential_data.add_sample(potential)
        potential_buffer.add_sample(round(potential, 3))
        if len(ocp_time_data.samples) == 0 and len(ocp_time_data.averagebuffer) > 0:
            ocp_outputfile.write(
                f"{ocp_time_data.averagebuffer[-1]:e}\t"
                f"{ocp_potential_data.averagebuffer[-1]:e}\n"
            )
            ocp_plot_curve.setData(ocp_time_data.averagebuffer, potential_buffer.averagebuffer)
            skipcounter = auto_current_range()


def ocp_stop(interrupted=True):
    global state, sequence_index
    sequence_index += 1
    if check_state([States.Measuring_OCP]):
        state = States.Idle_Init
        set_cell_status(False)
        ocp_outputfile.close()
        if interrupted:
            log_message("OCP measurement interrupted.")
        else:
            log_message("OCP measurement finished.")
        if sequence_flag == False:
            state = States.Stationary_Graph  # Keep displaying the last plot until the user clicks a button
            preview_cancel_button.show()
        if sequence_flag == True:
            state = States.Sequence_Idle
        GraphAutoExport(plot_frame, ocp_parameters['filename'])


def seq_ocp_start():
    global state, ocp_outputfile, ocp_plot_curve, ocp_time_data, ocp_potential_data, potential_buffer
    # print("seq_ocp_start")
    if check_state([States.Idle, States.Stationary_Graph, States.Sequence_Idle]) and sequence_flag and ocp_validate_parameters() and validate_file(ocp_parameters['filename'], overwrite_protect=False):
        ocp_starttime_text = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        ocp_endtime = datetime.datetime.now() + datetime.timedelta(seconds=ocp_parameters['duration'])
        ocp_end_text = ocp_endtime.strftime("%Y-%m-%d %H:%M:%S")
        ocp_outputfile = open(ocp_parameters['filename'], 'w', 1)  # 1 means line-buffered
        # do not change spacing below - it will change the fileheader
        ocp_outputfile.write(
            f"""Device Serial:\t{dev.serial_number}\nDuration[s]:\t{ocp_parameters['duration']}
                Start Time:\t{ocp_starttime_text}\nEstimated End:\t{ocp_end_text}
                Samples to Average:\t{ocp_parameters['numsamples']}\nElapsed_Time(s)\tPotential(V)\n"""
        )
        ocp_time_data = AverageBuffer(ocp_parameters['numsamples'])
        ocp_potential_data = AverageBuffer(ocp_parameters['numsamples'])
        potential_buffer = AverageBuffer(ocp_parameters['numsamples'])
        time.sleep(.1)  # Allow feedback loop some time to settle
        read_potential_current()
        time.sleep(.1)
        read_potential_current()  # Two reads are necessary because each read actually returns the result of the previous conversion

        preview_cancel_button.hide()
        try:  # Set up the plotting area
            legend.scene().removeItem(legend)
        except AttributeError:
            pass
        plot_frame.clear()
        plot_frame.enableAutoRange()
        # plot_frame.setXRange(0, 30, update=True)
        plot_frame.setLabel('bottom', 'Time', units="S")
        plot_frame.setLabel('left', 'Voltage', units="V")
        ocp_plot_curve = plot_frame.plot(pen=pen_color[0])  # Plot first cycle CV in yellow, changes with cycle number
        log_message("OCP measurement started. Saving to: %s" % ocp_parameters['filename'])
        state = States.Measuring_OCP
        ocp_parameters['starttime'] = timeit.default_timer()


def toggle_sequence_flag():
    global sequence_flag
    if sequence_flag == False:
        sequence_flag = True


def sequence_start():
    global test_sequence, sequence_index, sequence_flag, cd_voltage_finish_flag, cd_voltage_finish_mode, seq_cv_ocv_flag, state
    sequence_confirm_button.setEnabled(False)
    sequence_flag = True
    # print("sequence_start function")
    # print(f"sequence_index: {sequence_index}")
    # if sequence_index == 0:
    #     log_message("Sequence started")
    # print("test_sequence: ", test_sequence)
    if sequence_index >= len(test_sequence):
        sequence_flag = False
        log_message("Sequence finished.")
        state = States.Stationary_Graph  # Keep displaying the last plot until the user clicks a button
        preview_cancel_button.show()
        return
    else:
        log_message("Sequence " + str(sequence_index + 1) + " of " + str(len(test_sequence)) + " started")
    if test_sequence[sequence_index]['test_type'] == 'CV':
        cv_parameters['lbound'] = test_sequence[sequence_index]['lbound']
        cv_parameters['ubound'] = test_sequence[sequence_index]['ubound']
        if test_sequence[sequence_index]['auto_ocv'] == True:
            seq_cv_ocv_flag = True
            cv_parameters['startpot'] = cv_get_ocp()
            # print(f"OCV: {cv_parameters['startpot']}")
        elif test_sequence[sequence_index]['auto_ocv'] == False:
            seq_cv_ocv_flag = False
            cv_parameters['startpot'] = test_sequence[sequence_index]['startpot']
        cv_parameters['stoppot'] = test_sequence[sequence_index]['stoppot']
        cv_parameters['scanrate'] = test_sequence[sequence_index]['scanrate']
        cv_parameters['numcycles'] = test_sequence[sequence_index]['numcycles']
        cv_parameters['numsamples'] = test_sequence[sequence_index]['numsamples']
        cv_parameters['filename'] = test_sequence[sequence_index]['filename']
        # print(f"Starting CV: {cv_parameters['filename']}")
        seq_cv_start()
    elif test_sequence[sequence_index]['test_type'] == 'CCD':
        cd_parameters['lbound'] = test_sequence[sequence_index]['lbound']
        cd_parameters['ubound'] = test_sequence[sequence_index]['ubound']
        cd_parameters['chargecurrent'] = test_sequence[sequence_index]['chargecurrent']
        cd_parameters['dischargecurrent'] = test_sequence[sequence_index]['dischargecurrent']
        cd_parameters['numcycles'] = test_sequence[sequence_index]['numcycles']
        cd_parameters['numsamples'] = test_sequence[sequence_index]['numsamples']
        # cd_parameters['filename'] = test_sequence[sequence_index]['filename']
        cd_parameters['path'] = test_sequence[sequence_index]['path']
        cd_parameters['name'] = test_sequence[sequence_index]['name']
        cd_parameters['filename'] = cd_parameters['path'] + "/" + cd_parameters['name'] + ".csv"
        cd_voltage_finish_flag = test_sequence[sequence_index]['voltage_finish_flag']
        cd_voltage_finish_mode = test_sequence[sequence_index]['voltage_finish_mode']
        cd_parameters['voltage_finish_flag'] = test_sequence[sequence_index]['voltage_finish_flag']
        cd_parameters['voltage_finish_mode'] = test_sequence[sequence_index]['voltage_finish_mode']
        if cd_parameters['voltage_finish_flag']: #cd_voltage_finish_flag:
            # print("Voltage finish flag is true")
            if cd_parameters['voltage_finish_mode'] == 0: #cd_voltage_finish_mode == 0: #test_sequence[sequence_index]['voltage_finish_mode'] == 0:
                # print("Voltage finish mode is 0")
                # cd_parameters['voltage_finish_flag'] = True
                # cd_parameters['voltage_finish_mode'] = 0
                cd_parameters['finish_duration'] = test_sequence[sequence_index]['finish_duration']
                cd_parameters['chargecurrent_duration'] = 0
                cd_parameters['dischargecurrent_duration'] = 0
                # cd_parameters['current_duration'] = 0
            elif cd_parameters['voltage_finish_mode'] == 1: #cd_voltage_finish_mode == 1: #test_sequence[sequence_index]['voltage_finish_mode'] == 1:
                # print("Voltage finish mode is 1")
                # cd_parameters['voltage_finish_flag'] = True
                # cd_parameters['voltage_finish_mode'] = 1
                cd_parameters['finish_duration'] = 0
                # cd_parameters['current_duration'] = test_sequence[sequence_index]['current_duration']
                cd_parameters['chargecurrent_duration'] = test_sequence[sequence_index]['chargecurrent_duration']
                cd_parameters['dischargecurrent_duration'] = test_sequence[sequence_index]['dischargecurrent_duration']
            elif cd_parameters['voltage_finish_mode'] == 2: #cd_voltage_finish_mode == 2: #test_sequence[sequence_index]['voltage_finish_mode'] == 2:
                # print("Voltage finish mode is 2")
                # cd_parameters['voltage_finish_flag'] = True
                # cd_parameters['voltage_finish_mode'] = 2
                cd_parameters['finish_duration'] = test_sequence[sequence_index]['finish_duration']
                # cd_parameters['current_duration'] = test_sequence[sequence_index]['current_duration']
                cd_parameters['chargecurrent_duration'] = test_sequence[sequence_index]['chargecurrent_duration']
                cd_parameters['dischargecurrent_duration'] = test_sequence[sequence_index]['dischargecurrent_duration']
        # print(f"Starting CCD: {cd_parameters['filename']}")
        seq_cd_start()
    elif test_sequence[sequence_index]['test_type'] == 'Rate':
        rate_parameters['lbound'] = test_sequence[sequence_index]['lbound']
        rate_parameters['ubound'] = test_sequence[sequence_index]['ubound']
        rate_parameters['one_c_current'] = test_sequence[sequence_index]['one_c_current']
        rate_parameters['crates'] = test_sequence[sequence_index]['crates']
        rate_parameters['currents'] = test_sequence[sequence_index]['currents']
        rate_parameters['numcycles'] = test_sequence[sequence_index]['numcycles']
        rate_parameters['filename'] = test_sequence[sequence_index]['filename']
        # print(f"Starting Rate: {rate_parameters['filename']}")
        seq_rate_start()
    elif test_sequence[sequence_index]['test_type'] == 'OCP':
        ocp_parameters['duration'] = test_sequence[sequence_index]['duration']
        ocp_parameters['numsamples'] = test_sequence[sequence_index]['numsamples']
        ocp_parameters['filename'] = test_sequence[sequence_index]['filename']
        # print(f"Starting OCP: {ocp_parameters['filename']}")
        seq_ocp_start()
    else:
        pass
        # print("Error: Test type not recognized")

#-----------------------------------------------------------------------------------------------------------------------


# #--------------------------------------------------------------------------------------------------------------------
'''Redefines the QMainWindow's closeEvent functionality. This allows us to monitor for the application window's close button to be pressed
and to ask for confirmation first.'''
class MainWindow(QtWidgets.QMainWindow):
    # self.w = None
    def __init__(self):
        super().__init__()
        self.w = None

    def show_window(self, function):
        if function == "CV":
            self.w = SequenceCV()
            self.w.show()
        if function == "CCD":
            self.w = SequenceCD()
            self.w.show()
        if function == "Rate":
            self.w = SequenceRate()
            self.w.show()
        if function == "OCP":
            self.w = SequenceOCP()
            self.w.show()
        else:
            pass

    def update_window(self, function):
        if function == "CV":
            self.w = SequenceCV()
            self.w.seq_list_update()
            self.w.show()
        elif function == "CCD":
            self.w = SequenceCD()
            self.w.seq_list_update()
            self.w.show()
        elif function == "Rate":
            self.w = SequenceRate()
            self.w.seq_list_update()
            self.w.show()
        elif function == "OCP":
            self.w = SequenceOCP()
            self.w.seq_list_update()
            self.w.show()


    def closeEvent(self, event):
        reply = PyQt5.QtWidgets.QMessageBox.question(self, 'Window Close', 'Are you sure you want to close the window?',
                                                 PyQt5.QtWidgets.QMessageBox.Yes | PyQt5.QtWidgets.QMessageBox.No, PyQt5.QtWidgets.QMessageBox.No)

        if reply == PyQt5.QtWidgets.QMessageBox.Yes:
            event.accept()
            print('Window closed')
        else:
            event.ignore()


# Set up the GUI - Main Window --------------------------------------------------------------------------------------
app = QtWidgets.QApplication([])
#win = QtGui.QMainWindow()
win = MainWindow()
win.setGeometry(300, 300, 1024, 700)
win.setWindowTitle('USB potentiostat/galvanostat')
win.setWindowIcon(QtGui.QIcon('icon/icon.png'))

potential_monitor, potential_monitor_box = make_groupbox_indicator("Measured potential", "+#.### V")
potential_monitor.setFont(QtGui.QFont("monospace", 32))
current_monitor, current_monitor_box = make_groupbox_indicator("Measured current", "+#.### mA")
current_monitor.setFont(QtGui.QFont("monospace", 32))
potential_current_display_frame = QtWidgets.QHBoxLayout()
potential_current_display_frame.setSpacing(1)
potential_current_display_frame.setContentsMargins(0, 0, 0, 0)
potential_current_display_frame.addWidget(potential_monitor_box)
potential_current_display_frame.addWidget(current_monitor_box)

mode_display_frame = QtWidgets.QHBoxLayout()
mode_display_frame.setSpacing(1)
mode_display_frame.setContentsMargins(0, 0, 0, 5)
cell_status_monitor, cell_status_monitor_box = make_groupbox_indicator("Cell status", "        ")
cell_status_monitor.setFont(custom_size_font(14))
control_mode_monitor, control_mode_monitor_box = make_groupbox_indicator("Control mode", "             ")
control_mode_monitor.setFont(custom_size_font(14))
current_range_monitor, current_range_monitor_box = make_groupbox_indicator("Current range", "     ")
current_range_monitor.setFont(custom_size_font(14))
mode_display_frame.addWidget(cell_status_monitor_box)
mode_display_frame.addWidget(control_mode_monitor_box)
mode_display_frame.addWidget(current_range_monitor_box)
pyqtgraph.setConfigOptions(foreground="#e5e5e5", background="#00304f")
plot_frame = pyqtgraph.PlotWidget()

display_plot_frame = QtWidgets.QVBoxLayout()
display_plot_frame.setSpacing(0)
display_plot_frame.setContentsMargins(0, 0, 0, 0)
display_plot_frame.addLayout(potential_current_display_frame)
display_plot_frame.addLayout(mode_display_frame)
display_plot_frame.addWidget(plot_frame)

preview_cancel_vlayout = QtWidgets.QVBoxLayout(plot_frame)
preview_cancel_hlayout = QtWidgets.QHBoxLayout()
preview_cancel_vlayout.setAlignment(QtCore.Qt.AlignTop)
preview_cancel_vlayout.addLayout(preview_cancel_hlayout)
preview_cancel_hlayout.setAlignment(QtCore.Qt.AlignRight)
preview_cancel_button = QtWidgets.QPushButton("Back to live graph")
preview_cancel_button.clicked.connect(preview_cancel)
preview_cancel_hlayout.addWidget(preview_cancel_button)
preview_cancel_button.hide()

tab_frame = QtWidgets.QTabWidget()
tab_frame.setFixedWidth(500)

tab_names = ["Hardware", "CV", "Charge/disch.", "Rate testing", "OCP", "Sequence", "Temperature"]

tabs = [add_my_tab(tab_frame, tab_name) for tab_name in tab_names]

# Set up the GUI - Hardware tab --------------------------------------------------------------------------------------
hardware_vbox = QtWidgets.QVBoxLayout()
hardware_vbox.setAlignment(QtCore.Qt.AlignTop)

hardware_usb_box = QtWidgets.QGroupBox(title="USB Interface", flat=False)
format_box_for_parameter(hardware_usb_box)
hardware_usb_box_layout = QtWidgets.QVBoxLayout()
hardware_usb_box.setLayout(hardware_usb_box_layout)
# =============================================================================
# THIS SECTION IS THE ORIGINAL VID/PID DISPLAY CODE - Removed to implement serial number based connection!
# hardware_usb_vid_pid_layout = QtWidgets.QHBoxLayout()
# hardware_usb_box_layout.addLayout(hardware_usb_vid_pid_layout)
# hardware_usb_vid = make_label_entry(hardware_usb_vid_pid_layout, "VID")
# hardware_usb_vid.setText(usb_vid)
# hardware_usb_pid = make_label_entry(hardware_usb_vid_pid_layout, "PID")
# hardware_usb_pid.setText(usb_pid)
# =============================================================================
hardware_device_list_refreshButton = QtWidgets.QPushButton("Refresh Device List")
hardware_device_list_refreshButton.clicked.connect(usb_scan)
hardware_usb_box_layout.addWidget(hardware_device_list_refreshButton)
# =============================================================================
hardware_usb_device_list_layout = QtWidgets.QHBoxLayout()
hardware_usb_box_layout.addLayout(hardware_usb_device_list_layout)
hardware_usb_device_list_layout.addWidget(QtWidgets.QLabel("Device List"))
hardware_usb_device_list_dropdown = QtWidgets.QComboBox()
hardware_usb_device_list_dropdown.addItems(usb_device_list)
hardware_usb_device_list_layout.addWidget(hardware_usb_device_list_dropdown)
# hardware_manual_control_range_set_button = QtWidgets.QPushButton("Set")
# hardware_manual_control_range_set_button.clicked.connect(set_current_range)
# hardware_manual_control_range_layout.addWidget(hardware_manual_control_range_set_button)
# hardware_manual_control_box_layout.addLayout(hardware_manual_control_range_layout)
# =============================================================================
hardware_usb_connectButton = QtWidgets.QPushButton("Connect")
hardware_usb_connectButton.clicked.connect(connect_disconnect_usb)
hardware_usb_box_layout.addWidget(hardware_usb_connectButton)
# ======================================================
hardware_usb_box_layout.setSpacing(5)
hardware_usb_box_layout.setContentsMargins(3, 9, 3, 3)
hardware_vbox.addWidget(hardware_usb_box)

hardware_device_info_box = QtWidgets.QGroupBox(title="Device Information", flat=False)
format_box_for_parameter(hardware_device_info_box)
hardware_device_info_box_layout = QtWidgets.QVBoxLayout()
hardware_device_info_box.setLayout(hardware_device_info_box_layout)
hardware_device_info_text = QtWidgets.QLabel("Manufacturer: \nProduct: \nSerial #: ")
hardware_device_info_box_layout.addWidget(hardware_device_info_text)
hardware_device_info_box_layout.setSpacing(5)
hardware_device_info_box_layout.setContentsMargins(3, 9, 3, 3)
hardware_vbox.addWidget(hardware_device_info_box)

hardware_calibration_box = QtWidgets.QGroupBox(title="Calibration", flat=False)
format_box_for_parameter(hardware_calibration_box)
hardware_calibration_box_layout = QtWidgets.QVBoxLayout()
hardware_calibration_box.setLayout(hardware_calibration_box_layout)
hardware_calibration_dac_hlayout = QtWidgets.QHBoxLayout()
hardware_calibration_box_layout.addLayout(hardware_calibration_dac_hlayout)
hardware_calibration_dac_vlayout = QtWidgets.QVBoxLayout()
hardware_calibration_dac_hlayout.addLayout(hardware_calibration_dac_vlayout)
hardware_calibration_dac_offset = make_label_entry(hardware_calibration_dac_vlayout, "DAC Offset")
hardware_calibration_dac_offset.setToolTip("DAC Offset: ")
hardware_calibration_dac_gain = make_label_entry(hardware_calibration_dac_vlayout, "DAC Gain")
hardware_calibration_dac_gain.setToolTip("DAC Gain: ")
hardware_calibration_dac_calibrate_button = QtWidgets.QPushButton("Auto\nCalibrate")
hardware_calibration_dac_calibrate_button.setMaximumHeight(100)
hardware_calibration_dac_calibrate_button.clicked.connect(dac_calibrate)
hardware_calibration_dac_hlayout.addWidget(hardware_calibration_dac_calibrate_button)

hardware_calibration_offset_hlayout = QtWidgets.QHBoxLayout()
hardware_calibration_box_layout.addLayout(hardware_calibration_offset_hlayout)
hardware_calibration_offset_vlayout = QtWidgets.QVBoxLayout()
hardware_calibration_offset_hlayout.addLayout(hardware_calibration_offset_vlayout)
hardware_calibration_potential_offset = make_label_entry(hardware_calibration_offset_vlayout, "Pot. Offset")
hardware_calibration_potential_offset.setToolTip("Potential Offset: ")
hardware_calibration_potential_offset.editingFinished.connect(offset_changed_callback)
hardware_calibration_potential_offset.setText("0")
hardware_calibration_current_offset = make_label_entry(hardware_calibration_offset_vlayout, "Curr. Offset")
hardware_calibration_current_offset.setToolTip("Current Offset: ")
hardware_calibration_current_offset.editingFinished.connect(offset_changed_callback)
hardware_calibration_current_offset.setText("0")
hardware_calibration_adc_measure_button = QtWidgets.QPushButton("Auto\nZero")
hardware_calibration_adc_measure_button.setMaximumHeight(100)
hardware_calibration_adc_measure_button.clicked.connect(zero_offset)
hardware_calibration_offset_hlayout.addWidget(hardware_calibration_adc_measure_button)

hardware_calibration_shunt_resistor_layout = QtWidgets.QHBoxLayout()
hardware_calibration_box_layout.addLayout(hardware_calibration_shunt_resistor_layout)
hardware_calibration_shuntvalues = [make_label_entry(hardware_calibration_shunt_resistor_layout, "R%d" % i) for i in
                                    range(1, 4)]
for i in range(0, 3):
    hardware_calibration_shuntvalues[i].editingFinished.connect(shunt_calibration_changed_callback)
    hardware_calibration_shuntvalues[i].setText("%.4f" % shunt_calibration[i])

hardware_calibration_button_layout = QtWidgets.QHBoxLayout()
hardware_calibration_get_button = QtWidgets.QPushButton("Load from device")
hardware_calibration_get_button.clicked.connect(get_calibration)
hardware_calibration_button_layout.addWidget(hardware_calibration_get_button)
hardware_calibration_set_button = QtWidgets.QPushButton("Save to device")
hardware_calibration_set_button.clicked.connect(set_calibration)
hardware_calibration_button_layout.addWidget(hardware_calibration_set_button)

hardware_calibration_box_layout.addLayout(hardware_calibration_button_layout)
hardware_calibration_box_layout.setSpacing(3)
hardware_calibration_box_layout.setContentsMargins(3, 7, 3, 3)
hardware_vbox.addWidget(hardware_calibration_box)

hardware_manual_control_box = QtWidgets.QGroupBox(title="Manual Control", flat=False)
format_box_for_parameter(hardware_manual_control_box)
hardware_manual_control_box_layout = QtWidgets.QVBoxLayout()
hardware_manual_control_box.setLayout(hardware_manual_control_box_layout)

hardware_manual_control_cell_layout = QtWidgets.QHBoxLayout()
hardware_manual_control_cell_layout.addWidget(QtWidgets.QLabel("Cell connection"))
hardware_manual_control_cell_on_button = QtWidgets.QPushButton("On")
hardware_manual_control_cell_on_button.clicked.connect(lambda: set_cell_status(True))
hardware_manual_control_cell_layout.addWidget(hardware_manual_control_cell_on_button)
hardware_manual_control_cell_off_button = QtWidgets.QPushButton("Off")
hardware_manual_control_cell_off_button.clicked.connect(lambda: set_cell_status(False))
hardware_manual_control_cell_layout.addWidget(hardware_manual_control_cell_off_button)
hardware_manual_control_box_layout.addLayout(hardware_manual_control_cell_layout)

hardware_manual_control_mode_layout = QtWidgets.QHBoxLayout()
hardware_manual_control_mode_layout.addWidget(QtWidgets.QLabel("Mode"))
hardware_manual_control_mode_potentiostat_button = QtWidgets.QPushButton("Potentiostatic")
hardware_manual_control_mode_potentiostat_button.clicked.connect(lambda: set_control_mode(False))
hardware_manual_control_mode_layout.addWidget(hardware_manual_control_mode_potentiostat_button)
hardware_manual_control_mode_galvanostat_button = QtWidgets.QPushButton("Galvanostatic")
hardware_manual_control_mode_galvanostat_button.clicked.connect(lambda: set_control_mode(True))
hardware_manual_control_mode_layout.addWidget(hardware_manual_control_mode_galvanostat_button)
hardware_manual_control_box_layout.addLayout(hardware_manual_control_mode_layout)

hardware_manual_control_range_layout = QtWidgets.QHBoxLayout()
hardware_manual_control_range_layout.addWidget(QtWidgets.QLabel("Current range"))
hardware_manual_control_range_dropdown = QtWidgets.QComboBox()
hardware_manual_control_range_dropdown.addItems(current_range_list)
hardware_manual_control_range_layout.addWidget(hardware_manual_control_range_dropdown)
hardware_manual_control_range_set_button = QtWidgets.QPushButton("Set")
hardware_manual_control_range_set_button.clicked.connect(set_current_range)
hardware_manual_control_range_layout.addWidget(hardware_manual_control_range_set_button)
hardware_manual_control_box_layout.addLayout(hardware_manual_control_range_layout)

hardware_manual_control_output_layout = QtWidgets.QHBoxLayout()
hardware_manual_control_output_dropdown = QtWidgets.QComboBox()
hardware_manual_control_output_dropdown.addItems(units_list)
hardware_manual_control_output_layout.addWidget(hardware_manual_control_output_dropdown)
hardware_manual_control_output_entry = QtWidgets.QLineEdit()
hardware_manual_control_output_entry.returnPressed.connect(set_output_from_gui)
hardware_manual_control_output_layout.addWidget(hardware_manual_control_output_entry)
hardware_manual_control_output_set_button = QtWidgets.QPushButton("Set")
hardware_manual_control_output_set_button.clicked.connect(set_output_from_gui)
hardware_manual_control_output_layout.addWidget(hardware_manual_control_output_set_button)
hardware_manual_control_box_layout.addLayout(hardware_manual_control_output_layout)

hardware_manual_control_box_layout.setSpacing(5)
hardware_manual_control_box_layout.setContentsMargins(3, 9, 3, 3)

hardware_vbox.addWidget(hardware_manual_control_box)
# ==============================================================================
hardware_log_box = QtWidgets.QGroupBox(title="Log potential and current to file", flat=False)
format_box_for_parameter(hardware_log_box)
hardware_log_box_layout = QtWidgets.QHBoxLayout()
hardware_log_box.setLayout(hardware_log_box_layout)
hardware_log_checkbox = QtWidgets.QCheckBox("Log")
hardware_log_checkbox.stateChanged.connect(toggle_logging)
hardware_log_box_layout.addWidget(hardware_log_checkbox)
hardware_log_filename = QtWidgets.QLineEdit()
hardware_log_box_layout.addWidget(hardware_log_filename)
hardware_log_choose_button = QtWidgets.QPushButton("...")
hardware_log_choose_button.setFixedWidth(32)
hardware_log_choose_button.clicked.connect(
    lambda: choose_file(hardware_log_filename, "Choose where to save the log data"))
hardware_log_box_layout.addWidget(hardware_log_choose_button)

hardware_log_box_layout.setSpacing(5)
hardware_log_box_layout.setContentsMargins(3, 9, 3, 3)

hardware_vbox.addWidget(hardware_log_box)
# =========================================================================
error_log_box = QtWidgets.QGroupBox(title="Error Logging", flat=False)
format_box_for_parameter(error_log_box)
error_log_box_layout = QtWidgets.QHBoxLayout()
error_log_box.setLayout(error_log_box_layout)
error_log_checkbox = QtWidgets.QCheckBox("Log")
# error_log_checkbox.setTooltip("Test")
error_log_checkbox.stateChanged.connect(toggle_error_logging)
error_log_box_layout.addWidget(error_log_checkbox)
error_log_filename = QtWidgets.QLineEdit()
error_log_box_layout.addWidget(error_log_filename)
error_log_choose_button = QtWidgets.QPushButton("...")
error_log_choose_button.setToolTip("WARNING: ERROR LOG MAY BE SEVERAL GB IN SIZE, USE LINUX TO SPLIT")
error_log_choose_button.setFixedWidth(32)
error_log_choose_button.clicked.connect(
    lambda: choose_file(error_log_filename, "Choose where to save error logs"))
error_log_box_layout.addWidget(error_log_choose_button)


error_log_box_layout.setSpacing(5)
error_log_box_layout.setContentsMargins(3, 9, 3, 3)

hardware_vbox.addWidget(error_log_box)

hardware_vbox.setSpacing(6)
hardware_vbox.setContentsMargins(3, 3, 3, 3)

tabs[0].setLayout(hardware_vbox)

# Set up the GUI - CV tab ----------------------------------------------------------------------------------------------
cv_vbox = QtWidgets.QVBoxLayout()
cv_vbox.setAlignment(QtCore.Qt.AlignTop)

cv_params_box = QtWidgets.QGroupBox(title="Cyclic voltammetry parameters", flat=False)
format_box_for_parameter(cv_params_box)
cv_params_layout = QtWidgets.QVBoxLayout()
cv_params_box.setLayout(cv_params_layout)
cv_lbound_entry = make_label_entry(cv_params_layout, "Lower bound (V)")
cv_ubound_entry = make_label_entry(cv_params_layout, "Upper bound (V)")

cv_hbox = QtWidgets.QHBoxLayout()
cv_label = QtWidgets.QLabel(text="Start potential (V)")
cv_startpot_entry = QtWidgets.QLineEdit()
cv_get_button = QtWidgets.QPushButton("OCV")
cv_get_button.setFont(custom_size_font(8))
cv_get_button.setFixedWidth(32)
cv_get_button.clicked.connect(cv_get_ocp)

cv_hbox.addWidget(cv_label)
cv_hbox.addWidget(cv_startpot_entry)
cv_hbox.addWidget(cv_get_button)
cv_params_layout.addLayout(cv_hbox)

cv_stoppot_entry = make_label_entry(cv_params_layout, "Stop potential (V)")
cv_scanrate_entry = make_label_entry(cv_params_layout, "Scan rate (mV/s)")
cv_scanrate_entry.setToolTip("Maximum Scan Rate: 500mV/s (45mV Step)")
cv_scanrate_entry.editingFinished.connect(cv_scanrate_changed_callback)
cv_numcycles_entry = make_label_entry(cv_params_layout, "Number of cycles")
cv_numcycles_entry.editingFinished.connect(cv_numcycles_changed_callback)
cv_numsamples_entry = make_label_entry(cv_params_layout, "Samples to average")
cv_numsamples_entry.setToolTip("Time between data points: n x 90E-3 seconds")
cv_numsamples_entry.setText("1")

cv_params_layout.setSpacing(6)
cv_params_layout.setContentsMargins(3, 10, 3, 3)
cv_vbox.addWidget(cv_params_box)

cv_range_box = QtWidgets.QGroupBox(title="Autoranging", flat=False)
format_box_for_parameter(cv_range_box)
cv_range_layout = QtWidgets.QVBoxLayout()
cv_range_box.setLayout(cv_range_layout)
cv_range_checkboxes = []
for current in current_range_list:
    checkbox = QtWidgets.QCheckBox(current)
    cv_range_checkboxes.append(checkbox)
    cv_range_layout.addWidget(checkbox)
    checkbox.setChecked(True)

cv_range_layout.setSpacing(6)
cv_range_layout.setContentsMargins(3, 10, 3, 3)
cv_vbox.addWidget(cv_range_box)

cv_file_box = QtWidgets.QGroupBox(title="Output data filename", flat=False)
format_box_for_parameter(cv_file_box)
cv_file_layout = QtWidgets.QVBoxLayout()
cv_file_box.setLayout(cv_file_layout)
cv_file_choose_layout = QtWidgets.QHBoxLayout()
cv_file_entry = QtWidgets.QLineEdit()
cv_file_choose_layout.addWidget(cv_file_entry)
cv_file_choose_button = QtWidgets.QPushButton("...")
cv_file_choose_button.setFixedWidth(32)
cv_file_choose_layout.addWidget(cv_file_choose_button)
cv_file_choose_button.clicked.connect(
    lambda: choose_file(cv_file_entry, "Choose where to save the CV measurement data"))
cv_file_layout.addLayout(cv_file_choose_layout)
cv_file_layout.setSpacing(6)
cv_file_layout.setContentsMargins(3, 10, 3, 3)
cv_vbox.addWidget(cv_file_box)

cv_time_calculator_box = QtWidgets.QGroupBox(title="Timing Estimates", flat=False)
format_box_for_parameter(cv_time_calculator_box)
cv_time_calculator_box_layout = QtWidgets.QVBoxLayout()
cv_time_calculator_box.setLayout(cv_time_calculator_box_layout)
cv_time_calculator_text = QtWidgets.QLabel("Duration: \nStart: \nEst. End: ")
cv_time_calculator_box_layout.addWidget(cv_time_calculator_text)
cv_time_calculator_box_layout.setSpacing(5)
cv_time_calculator_box_layout.setContentsMargins(3, 9, 3, 3)
cv_vbox.addWidget(cv_time_calculator_box)

cv_preview_button = QtWidgets.QPushButton("Preview sweep")
cv_preview_button.clicked.connect(cv_preview)
cv_vbox.addWidget(cv_preview_button)
cv_start_button = QtWidgets.QPushButton("Start cyclic voltammetry")
cv_start_button.clicked.connect(cv_start)
cv_vbox.addWidget(cv_start_button)
cv_stop_button = QtWidgets.QPushButton("Stop cyclic voltammetry")
cv_stop_button.clicked.connect(lambda: cv_stop(interrupted=True))
cv_vbox.addWidget(cv_stop_button)

cv_vbox.setSpacing(6)
cv_vbox.setContentsMargins(3, 3, 3, 3)

tabs[1].setLayout(cv_vbox)

# Set up the GUI - charge/discharge tab ------------------------------------------------------------------------------
cd_vbox = QtWidgets.QVBoxLayout()
cd_vbox.setAlignment(QtCore.Qt.AlignTop)

cd_params_box = QtWidgets.QGroupBox(title="Charge/discharge parameters", flat=False)
format_box_for_parameter(cd_params_box)
cd_params_layout = QtWidgets.QVBoxLayout()
cd_params_box.setLayout(cd_params_layout)
cd_lbound_entry = make_label_entry(cd_params_layout, "Lower bound (V)")
cd_ubound_entry = make_label_entry(cd_params_layout, "Upper bound (V)")
cd_chargecurrent_entry = make_label_entry(cd_params_layout, u"Charge current (µA)")
cd_chargecurrent_entry.setToolTip("(+) -> 1st Cycle Charge / (-) -> 1st Cycle Discharge")
cd_dischargecurrent_entry = make_label_entry(cd_params_layout, u"Discharge current (µA)")
cd_dischargecurrent_entry.setToolTip("+/- sign must be opposite of Charge Current")
cd_numcycles_entry = make_label_entry(cd_params_layout, "Number of half cycles")
cd_numsamples_entry = make_label_entry(cd_params_layout, "Samples to average")
cd_numsamples_entry.setText("5")

voltage_finish_vbox = QtWidgets.QGroupBox(title="Voltage finish", flat=False)
voltage_finish_vbox_layout = QtWidgets.QVBoxLayout()
voltage_finish_vbox.setLayout(voltage_finish_vbox_layout)

voltage_finish_box = QtWidgets.QGroupBox(title="", flat=False)
finish_selection_layout = QtWidgets.QHBoxLayout()
voltage_finish_box.setLayout(finish_selection_layout)

voltage_finish_checkbox = QtWidgets.QCheckBox("Enable voltage finish")
voltage_finish_checkbox.stateChanged.connect(toggle_voltage_finish)
voltage_finish_vbox_layout.addWidget(voltage_finish_checkbox)

voltage_finish_time_radio = make_radio_entry(finish_selection_layout, "Time (s)")
voltage_finish_time_radio.setChecked(True)
voltage_finish_time_radio.setEnabled(False)
voltage_finish_current_radio = make_radio_entry(finish_selection_layout, "Current (µA)")
voltage_finish_current_radio.setEnabled(False)
voltage_finish_both_radio = make_radio_entry(finish_selection_layout, "Time and current")
voltage_finish_both_radio.setEnabled(False)
voltage_finish_time_radio.clicked.connect(lambda: set_voltage_finish_mode())
voltage_finish_current_radio.clicked.connect(lambda: set_voltage_finish_mode())
voltage_finish_both_radio.clicked.connect(lambda: set_voltage_finish_mode())

voltage_finish_vbox_layout.addWidget(voltage_finish_box)
voltage_finish_time_entry = make_label_entry(voltage_finish_vbox_layout, "Time (s)")
voltage_finish_time_entry.setEnabled(False)
voltage_finish_chargecurrent_entry = make_label_entry(voltage_finish_vbox_layout, "Charge Tapering Limit (µA)")
voltage_finish_chargecurrent_entry.setToolTip("+/- sign must match that in charge current entry")
voltage_finish_chargecurrent_entry.setEnabled(False)
voltage_finish_dischargecurrent_entry = make_label_entry(voltage_finish_vbox_layout, "Discharge Tapering Limit (µA)")
voltage_finish_dischargecurrent_entry.setToolTip("+/- sign must match that in discharge current entry")
voltage_finish_dischargecurrent_entry.setEnabled(False)
cd_params_layout.addWidget(voltage_finish_vbox)

cd_params_layout.setSpacing(6)
cd_params_layout.setContentsMargins(3, 10, 3, 3)
cd_vbox.addWidget(cd_params_box)

cd_file_box = QtWidgets.QGroupBox(title="Output data filename", flat=False)
format_box_for_parameter(cd_file_box)
cd_file_layout = QtWidgets.QVBoxLayout()
cd_file_box.setLayout(cd_file_layout)
cd_file_choose_layout = QtWidgets.QHBoxLayout()
cd_file_entry = QtWidgets.QLineEdit()
cd_file_choose_layout.addWidget(cd_file_entry)
cd_file_choose_button = QtWidgets.QPushButton("...")
cd_file_choose_button.setFixedWidth(32)
cd_file_choose_layout.addWidget(cd_file_choose_button)
cd_file_choose_button.clicked.connect(
    lambda: choose_file(cd_file_entry, "Choose where to save the charge/discharge measurement data"))
cd_file_layout.addLayout(cd_file_choose_layout)
cd_file_layout.setSpacing(6)
cd_file_layout.setContentsMargins(3, 10, 3, 3)
cd_vbox.addWidget(cd_file_box)

cd_start_button = QtWidgets.QPushButton("Start charge/discharge")
cd_start_button.clicked.connect(cd_start)
cd_vbox.addWidget(cd_start_button)
cd_stop_button = QtWidgets.QPushButton("Stop charge/discharge")
cd_stop_button.clicked.connect(lambda: cd_stop(interrupted=True))
cd_vbox.addWidget(cd_stop_button)

cd_vbox.setSpacing(6)
cd_vbox.setContentsMargins(3, 3, 3, 3)

cd_info_box = QtWidgets.QGroupBox(title="Information", flat=False)
format_box_for_parameter(cd_info_box)
cd_info_layout = QtWidgets.QVBoxLayout()
cd_info_box.setLayout(cd_info_layout)
cd_current_cycle_entry = make_label_entry(cd_info_layout, "Current half cycle")
cd_current_cycle_entry.setReadOnly(True)

cd_info_layout.setSpacing(6)
cd_info_layout.setContentsMargins(3, 10, 3, 3)
cd_vbox.addWidget(cd_info_box)

tabs[2].setLayout(cd_vbox)

# Set up the GUI - Rate testing tab --------------------------------------------------------------------------------
rate_vbox = QtWidgets.QVBoxLayout()
rate_vbox.setAlignment(QtCore.Qt.AlignTop)

rate_params_box = QtWidgets.QGroupBox(title="Rate testing parameters", flat=False)
format_box_for_parameter(rate_params_box)
rate_params_layout = QtWidgets.QVBoxLayout()
rate_params_box.setLayout(rate_params_layout)
rate_lbound_entry = make_label_entry(rate_params_layout, "Lower bound (V)")
rate_ubound_entry = make_label_entry(rate_params_layout, "Upper bound (V)")
rate_capacity_entry = make_label_entry(rate_params_layout, u"C (µAh)")
rate_crates_entry = make_label_entry(rate_params_layout, u"C-rates")
rate_crates_entry.setText("1, 2, 5, 10, 20, 50, 100")
rate_numcycles_entry = make_label_entry(rate_params_layout, u"Cycles per C-rate")

rate_params_layout.setSpacing(6)
rate_params_layout.setContentsMargins(3, 10, 3, 3)
rate_vbox.addWidget(rate_params_box)

rate_file_box = QtWidgets.QGroupBox(title="Output data filename", flat=False)
format_box_for_parameter(rate_file_box)
rate_file_layout = QtWidgets.QVBoxLayout()
rate_file_box.setLayout(rate_file_layout)
rate_file_choose_layout = QtWidgets.QHBoxLayout()
rate_file_entry = QtWidgets.QLineEdit()
rate_file_choose_layout.addWidget(rate_file_entry)
rate_file_choose_button = QtWidgets.QPushButton("...")
rate_file_choose_button.setFixedWidth(32)
rate_file_choose_button.clicked.connect(
    lambda: choose_file(rate_file_entry, "Choose where to save the rate testing measurement data"))
rate_file_choose_layout.addWidget(rate_file_choose_button)
rate_file_layout.addLayout(rate_file_choose_layout)

rate_file_layout.setSpacing(6)
rate_file_layout.setContentsMargins(3, 10, 3, 3)
rate_vbox.addWidget(rate_file_box)

rate_start_button = QtWidgets.QPushButton("Start Rate Test")
rate_start_button.clicked.connect(rate_start)
rate_vbox.addWidget(rate_start_button)
rate_stop_button = QtWidgets.QPushButton("Stop Rate Test")
rate_stop_button.clicked.connect(lambda: rate_stop(interrupted=True))
rate_vbox.addWidget(rate_stop_button)

rate_vbox.setSpacing(6)
rate_vbox.setContentsMargins(3, 3, 3, 3)

rate_info_box = QtWidgets.QGroupBox(title="Information", flat=False)
format_box_for_parameter(rate_info_box)
rate_info_layout = QtWidgets.QVBoxLayout()
rate_info_box.setLayout(rate_info_layout)
rate_current_crate_entry = make_label_entry(rate_info_layout, "Current C-rate")
rate_current_crate_entry.setReadOnly(True)

rate_info_layout.setSpacing(6)
rate_info_layout.setContentsMargins(3, 10, 3, 3)
rate_vbox.addWidget(rate_info_box)

tabs[3].setLayout(rate_vbox)
# Set up the GUI - OCP Testing -----------------------------------------------------------------------------------
ocp_vbox = QtWidgets.QVBoxLayout()
ocp_vbox.setAlignment(QtCore.Qt.AlignTop)

ocp_params_box = QtWidgets.QGroupBox(title="OCP testing parameters", flat=False)
format_box_for_parameter(ocp_params_box)
ocp_params_layout = QtWidgets.QVBoxLayout()
ocp_params_box.setLayout(ocp_params_layout)
ocp_duration_entry = make_label_entry(ocp_params_layout, "Duration (s)")
ocp_numsamples_entry = make_label_entry(ocp_params_layout, "Samples to Average")
ocp_duration_entry.setText('30')
ocp_numsamples_entry.setText('5')

ocp_params_layout.setSpacing(6)
ocp_params_layout.setContentsMargins(3, 10, 3, 3)
ocp_vbox.addWidget(ocp_params_box)

ocp_file_box = QtWidgets.QGroupBox(title="Output data filename", flat=False)
format_box_for_parameter(ocp_file_box)
ocp_file_layout = QtWidgets.QVBoxLayout()
ocp_file_box.setLayout(ocp_file_layout)
ocp_file_choose_layout = QtWidgets.QHBoxLayout()
ocp_file_entry = QtWidgets.QLineEdit()
ocp_file_choose_layout.addWidget(ocp_file_entry)
ocp_file_choose_button = QtWidgets.QPushButton("...")
ocp_file_choose_button.setFixedWidth(32)
ocp_file_choose_button.clicked.connect(
    lambda: choose_file(ocp_file_entry, "Choose where to save the OCP testing measurement data"))
ocp_file_choose_layout.addWidget(ocp_file_choose_button)
ocp_file_layout.addLayout(ocp_file_choose_layout)

ocp_file_layout.setSpacing(6)
ocp_file_layout.setContentsMargins(3, 10, 3, 3)
ocp_vbox.addWidget(ocp_file_box)

ocp_start_button = QtWidgets.QPushButton("Start OCP Test")
ocp_start_button.clicked.connect(ocp_start)
ocp_vbox.addWidget(ocp_start_button)
ocp_stop_button = QtWidgets.QPushButton("Stop OCP Test")
ocp_stop_button.clicked.connect(lambda: ocp_stop(interrupted=True))
ocp_vbox.addWidget(ocp_stop_button)

ocp_vbox.setSpacing(6)
ocp_vbox.setContentsMargins(3, 3, 3, 3)

tabs[4].setLayout(ocp_vbox)
# Set up the GUI - Sequence Testing -----------------------------------------------------------------------------------

sequence_vbox = QtWidgets.QVBoxLayout()
sequence_vbox.setAlignment(QtCore.Qt.AlignTop)

sequence_file_box = QtWidgets.QGroupBox(title="Output data directory", flat=False)
format_box_for_parameter(sequence_file_box)
sequence_file_layout = QtWidgets.QVBoxLayout()
sequence_file_box.setLayout(sequence_file_layout)
sequence_file_choose_layout = QtWidgets.QHBoxLayout()
sequence_file_entry = QtWidgets.QLineEdit()
sequence_file_choose_layout.addWidget(sequence_file_entry)
sequence_file_choose_button = QtWidgets.QPushButton("...")
sequence_file_choose_button.setFixedWidth(32)
sequence_file_choose_button.clicked.connect(
    lambda: choose_directory(sequence_file_entry, "Choose root directory to store tests"))
sequence_file_choose_layout.addWidget(sequence_file_choose_button)
sequence_file_layout.addLayout(sequence_file_choose_layout)

sequence_file_layout.setSpacing(6)
sequence_file_layout.setContentsMargins(3, 10, 3, 3)
sequence_vbox.addWidget(sequence_file_box)

sequence_template_box = QtWidgets.QGroupBox(title="Sequence template", flat=False)
format_box_for_parameter(sequence_template_box)
sequence_template_layout = QtWidgets.QVBoxLayout()
sequence_template_box.setLayout(sequence_template_layout)

sequence_template_file_choose_layout = QtWidgets.QHBoxLayout()
sequence_template_file_entry = QtWidgets.QLineEdit()
sequence_template_file_choose_layout.addWidget(sequence_template_file_entry)
sequence_template_file_choose_button = QtWidgets.QPushButton("...")
sequence_template_file_choose_button.setFixedWidth(32)
sequence_template_file_choose_layout.addWidget(sequence_template_file_choose_button)
sequence_template_file_choose_button.clicked.connect(
    lambda: choose_file(sequence_template_file_entry, "Select a sequence template file or create a new one"))


sequence_loadsave_layout = QtWidgets.QHBoxLayout()
sequence_template_load_button = QtWidgets.QPushButton("Load template sequence")
sequence_template_load_button.clicked.connect(lambda: seq_template_load())
sequence_loadsave_layout.addWidget(sequence_template_load_button)
sequence_template_save_button = QtWidgets.QPushButton("Save template sequence")
sequence_template_save_button.clicked.connect(lambda: seq_template_save())
sequence_loadsave_layout.addWidget(sequence_template_save_button)
# sequence_loadsave_layout.setSpacing(6)
# sequence_loadsave_layout.setContentsMargins(3, 10, 3, 3)

sequence_template_layout.addLayout(sequence_template_file_choose_layout)
sequence_template_layout.addLayout(sequence_loadsave_layout)
sequence_template_layout.setSpacing(6)
sequence_template_layout.setContentsMargins(3, 10, 3, 3)

sequence_vbox.addWidget(sequence_template_box)
sequence_template_file_entry.setEnabled(False)
sequence_template_file_choose_button.setEnabled(False)
sequence_template_load_button.setEnabled(False)
sequence_template_save_button.setEnabled(False)

sequence_params_box = QtWidgets.QGroupBox(title="Sequence Builder", flat=False)
sequence_params_layout = QtWidgets.QVBoxLayout()
format_box_for_parameter(sequence_params_box)
sequence_radio_layout = QtWidgets.QHBoxLayout()
sequence_params_box.setLayout(sequence_params_layout)
sequence_cvradio_entry = make_radio_entry(sequence_radio_layout, "CV")
sequence_cvradio_entry.setChecked(True)
sequence_cdradio_entry = make_radio_entry(sequence_radio_layout, "CCD")
sequence_rateradio_entry = make_radio_entry(sequence_radio_layout, "Rate")
sequence_ocvradio_entry = make_radio_entry(sequence_radio_layout, "OCP")
sequence_cvradio_entry.setEnabled(False)
sequence_cdradio_entry.setEnabled(False)
sequence_rateradio_entry.setEnabled(False)
sequence_ocvradio_entry.setEnabled(False)

sequence_test_add_button = QtWidgets.QPushButton("Add Test")
sequence_test_add_button.setEnabled(False)
sequence_file_entry.textChanged.connect(lambda: check_button())
sequence_test_add_button.clicked.connect(lambda: call_list_popup())
sequence_test_remove_button = QtWidgets.QPushButton("Remove Test")
sequence_test_remove_button.clicked.connect(lambda: remove_test(sequence_test_list, sequence_test_list.currentRow()))
sequence_test_button_layout = QtWidgets.QHBoxLayout()
sequence_test_button_layout.addWidget(sequence_test_add_button)
sequence_test_button_layout.addWidget(sequence_test_remove_button)

sequence_radio_layout.setSpacing(6)
sequence_radio_layout.setContentsMargins(3, 10, 3, 3)
sequence_params_layout.addLayout(sequence_radio_layout)
sequence_params_layout.addLayout(sequence_test_button_layout)

sequence_test_list = QtWidgets.QListWidget()
sequence_params_layout.addWidget(sequence_test_list)
sequence_test_list.setDragDropMode(QtWidgets.QAbstractItemView.InternalMove)
sequence_test_list.itemDoubleClicked.connect(lambda: seq_view_list())
sequence_test_list.model().rowsMoved.connect(lambda: seq_list_changed())

sequence_confirm_button = QtWidgets.QPushButton("Confirm Test Order")
sequence_confirm_button.clicked.connect(lambda: confirm_test())
sequence_params_layout.addWidget(sequence_confirm_button)

sequence_vbox.addWidget(sequence_params_box)

sequence_start_button = QtWidgets.QPushButton("Start Test Sequence")
sequence_start_button.setEnabled(False)
sequence_start_button.clicked.connect(lambda: sequence_start())
sequence_vbox.addWidget(sequence_start_button)

sequence_test_stop_button = QtWidgets.QPushButton("Skip Current Test")
sequence_test_stop_button.clicked.connect(lambda: seq_skip_test())
sequence_vbox.addWidget(sequence_test_stop_button)

sequence_stop_button = QtWidgets.QPushButton("Stop Test Sequence")
sequence_stop_button.clicked.connect(lambda: seq_stop_all())
sequence_vbox.addWidget(sequence_stop_button)

sequence_vbox.setSpacing(6)
sequence_vbox.setContentsMargins(3, 3, 3, 3)

sequence_info_box = QtWidgets.QGroupBox(title="Information", flat=False)
format_box_for_parameter(sequence_info_box)
sequence_info_layout = QtWidgets.QVBoxLayout()
sequence_info_box.setLayout(sequence_info_layout)
sequence_current_crate_entry = make_label_entry(sequence_info_layout, "Current C-rate")
sequence_current_crate_entry.setReadOnly(True)

sequence_info_layout.setSpacing(6)
sequence_info_layout.setContentsMargins(3, 10, 3, 3)
sequence_vbox.addWidget(sequence_info_box)

tabs[5].setLayout(sequence_vbox)
# ----------------------------------------------------------
temp_vbox = QtWidgets.QVBoxLayout()
temp_vbox.setAlignment(QtCore.Qt.AlignTop)

temp_params_box = QtWidgets.QGroupBox(title="Temperature Measurement Parameters", flat=False)
format_box_for_parameter(temp_params_box)
temp_params_layout = QtWidgets.QVBoxLayout()
temp_params_box.setLayout(temp_params_layout)


tempsensor_radio_layout = QtWidgets.QHBoxLayout()
temp_type_label_entry = QtWidgets.QLabel("Temperature Sensor Type:")
tempsensor_radio_layout.addWidget(temp_type_label_entry)
temp_pt100_radio_entry = make_radio_entry(tempsensor_radio_layout, "PT100")
temp_pt1000_radio_entry = make_radio_entry(tempsensor_radio_layout, "PT1000")
temp_pt1000_radio_entry.setChecked(True)
tempsensor_radio_layout.setSpacing(6)
tempsensor_radio_layout.setContentsMargins(3, 10, 3, 3)
temp_params_layout.addLayout(tempsensor_radio_layout)

temp_duration_layout = QtWidgets.QHBoxLayout()
temp_duration_label_entry = QtWidgets.QLabel("Duration:")
temp_duration_layout.addWidget(temp_duration_label_entry)
temp_duration_days = make_label_entry(temp_duration_layout, "Days:")
temp_duration_days.setText("0")
temp_duration_hours = make_label_entry(temp_duration_layout, "Hours:")
temp_duration_hours.setText("0")
temp_duration_minutes = make_label_entry(temp_duration_layout, "Minutes:")
temp_duration_minutes.setText("0")
temp_duration_seconds = make_label_entry(temp_duration_layout, "Seconds:")
temp_duration_seconds.setText("0")
temp_duration_layout.setSpacing(10)
temp_duration_layout.setContentsMargins(3, 10, 3, 3)
temp_params_layout.addLayout(temp_duration_layout)

plotinterval_hbox = QtWidgets.QHBoxLayout()
plotinterval_label_entry = QtWidgets.QLabel("Plot Interval:")
plotinterval_hbox.addWidget(plotinterval_label_entry)
plotinterval_combobox = QtWidgets.QComboBox()
plotintervals = ["1 second", "5 seconds", "15 seconds", "30 seconds", "1 minute", "5 minutes", "10 minutes", "15 minutes", "Custom"]
for item in plotintervals:
    plotinterval_combobox.addItem(item)
plotinterval_combobox.setCurrentIndex(2)
plotinterval_combobox.currentIndexChanged.connect(lambda: plotinterval_changed())
plotinterval_hbox.addWidget(plotinterval_combobox)
plotinterval_hbox.setSpacing(6)
plotinterval_hbox.setContentsMargins(3, 10, 3, 3)
temp_params_layout.addLayout(plotinterval_hbox)
plotinterval_custom_entry = make_label_entry(temp_params_layout, "Custom Interval (s):")
plotinterval_custom_entry.setText("1")
plotinterval_custom_entry.setEnabled(False)

# target_temp_entry = make_label_entry(temp_params_layout, "Target Temperature (Degrees Celcius):")
# target_temp_stableduration_entry = make_label_entry(temp_params_layout, "Target Temperature Stable Duration (s):")

temp_file_box = QtWidgets.QGroupBox(title="Output data filename", flat=False)
format_box_for_parameter(temp_file_box)
temp_file_layout = QtWidgets.QVBoxLayout()
temp_file_box.setLayout(temp_file_layout)
temp_file_choose_layout = QtWidgets.QHBoxLayout()
temp_file_entry = QtWidgets.QLineEdit()
temp_file_choose_layout.addWidget(temp_file_entry)
temp_file_choose_button = QtWidgets.QPushButton("...")
temp_file_choose_button.setFixedWidth(32)
temp_file_choose_button.clicked.connect(
    lambda: choose_file(temp_file_entry, "Choose where to save the temperature measurement data"))
temp_file_choose_layout.addWidget(temp_file_choose_button)
temp_file_layout.addLayout(temp_file_choose_layout)
temp_file_layout.setSpacing(6)
temp_file_layout.setContentsMargins(3, 10, 3, 3)

temp_start_button = QtWidgets.QPushButton("Start Temperature Measurement")
temp_start_button.clicked.connect(lambda: start_temp_measurement())
temp_stop_button = QtWidgets.QPushButton("Stop Temperature Measurement")
temp_stop_button.clicked.connect(lambda: stop_temp_measurement(interrupted=True))

temperature_monitor, temperature_monitor_box = make_groupbox_indicator("Current Temperature:", "+#.## \u2103")
temperature_monitor.setFont(QtGui.QFont("monospace", 32))

temp_vbox.addWidget(temperature_monitor_box)
temp_vbox.addWidget(temp_params_box)
temp_vbox.addWidget(temp_file_box)
temp_vbox.addWidget(temp_start_button)
temp_vbox.addWidget(temp_stop_button)
temp_vbox.setSpacing(6)
temp_vbox.setContentsMargins(3, 3, 3, 3)

tabs[6].setLayout(temp_vbox)
# ------------------------------------------------------------------------------------------
# Sequence Pop-up Functions


def check_button():
    checkforentry = sequence_file_entry.text()
    if checkforentry:
        sequence_test_add_button.setEnabled(True)
        sequence_cvradio_entry.setEnabled(True)
        sequence_cdradio_entry.setEnabled(True)
        sequence_rateradio_entry.setEnabled(True)
        sequence_ocvradio_entry.setEnabled(True)
        sequence_template_file_entry.setEnabled(True)
        sequence_template_file_choose_button.setEnabled(True)
        sequence_template_load_button.setEnabled(True)
        sequence_template_save_button.setEnabled(True)


def call_list_popup():
    if sequence_cvradio_entry.isChecked():
        MainWindow.show_window(win, sequence_cvradio_entry.text())
    if sequence_cdradio_entry.isChecked():
        MainWindow.show_window(win, sequence_cdradio_entry.text())
    if sequence_rateradio_entry.isChecked():
        MainWindow.show_window(win, sequence_rateradio_entry.text())
    if sequence_ocvradio_entry.isChecked():
        MainWindow.show_window(win, sequence_ocvradio_entry.text())
    else:
        pass


def seq_cv_getparams(self):
    """Retrieve the CV parameters from the GUI input fields and store them in a global dictionary. If succesful, return True."""
    global cv_parameters, seq_cv_ocv_flag
    try:
        cv_parameters['lbound'] = float(self.sequence_cv_lbound_entry.text())
        cv_parameters['ubound'] = float(self.sequence_cv_ubound_entry.text())
        if seq_cv_ocv_flag:
            cv_parameters['auto_ocv'] = True
            cv_parameters['startpot'] = 0 #  This is a dummy value, used to pass cv_validate_parameters
        else:
            cv_parameters['startpot'] = float(self.sequence_cv_startpot_entry.text())
            cv_parameters['auto_ocv'] = False
        cv_parameters['stoppot'] = float(self.sequence_cv_stoppot_entry.text())
        cv_parameters['scanrate'] = float(self.sequence_cv_scanrate_entry.text()) / 1e3  # Convert to V/s
        cv_parameters['numcycles'] = int(self.sequence_cv_numcycles_entry.text())
        cv_parameters['numsamples'] = int(self.sequence_cv_numsamples_entry.text())
        cv_parameters['path'] = str(sequence_file_entry.text())
        cv_parameters['name'] = str(self.sequence_cv_file_entry.text())
        cv_parameters['filename'] = cv_parameters['path'] + "/" + cv_parameters['name'] + ".csv"
        # cv_parameters['filename'] = str(sequence_file_entry.text()) + "/" + str(self.sequence_cv_file_entry.text()) + ".csv"
        # initialtime = cv_parameters['ubound'] - cv_parameters['startpot']
        # cycletime = (cv_parameters['ubound'] - cv_parameters['lbound']) * 2. * cv_parameters['numcycles']
        # finaltime = abs(cv_parameters['stoppot'] - cv_parameters['ubound'])
        # cv_parameters['duration'] = (initialtime + cycletime + finaltime) / (cv_parameters['scanrate'])# / 1000)
        # print(f'duration: {cv_parameters["duration"]}')
        # # cv_duration_text = duration_to_text_days_hours(cv_parameters['duration'])
        return True
    except ValueError:
        QtWidgets.QMessageBox.critical(mainwidget, "Not a number",
                                   "One or more parameters could not be interpreted as a number.")
        return False


def seq_cv_listing(self, listname):
    global cv_parameters, seq_cv_ocv_flag
    # seq_cv_getparams(self)
    if seq_cv_getparams(self) and cv_validate_parameters():# and validate_file(cv_parameters['filename'], overwrite_protect=True):
        listname.addItem(cv_parameters['filename'])
        items = listname.findItems(cv_parameters['filename'], QtCore.Qt.MatchExactly)
        if len(items) > 0:
            for item in items:
                i = listname.row(item)
        test_sequence[i] = {}
        test_sequence[i]['test_key'] = i
        test_sequence[i]['test_type'] = 'CV'
        test_sequence[i].update(cv_parameters)
        seq_cv_ocv_flag = False
        self.close()



def seq_cd_getparams(self):
    """Retrieve the charge/discharge parameters from the GUI input fields and store them in a global dictionary. If succesful, return True."""
    global cd_parameters, cd_voltage_finish_flag, cd_voltage_finish_mode
    # print("seq_cd_getparams")
    try:
        cd_parameters['lbound'] = float(self.sequence_cd_lbound_entry.text())
        cd_parameters['ubound'] = float(self.sequence_cd_ubound_entry.text())
        cd_parameters['chargecurrent'] = float(self.sequence_cd_chargecurrent_entry.text()) / 1e3  # convert uA to mA
        cd_parameters['dischargecurrent'] = float(self.sequence_cd_dischargecurrent_entry.text()) / 1e3  # convert uA to mA
        cd_parameters['numcycles'] = int(self.sequence_cd_numcycles_entry.text())
        cd_parameters['numsamples'] = int(self.sequence_cd_numsamples_entry.text())
        cd_parameters['path'] = str(sequence_file_entry.text())
        cd_parameters['name'] = str(self.sequence_cd_file_entry.text())
        cd_parameters['filename'] = cd_parameters['path'] + "/" + cd_parameters['name'] + ".csv"
        # cd_parameters['filename'] = str(sequence_file_entry.text()) + "/" + str(self.sequence_cd_file_entry.text()) + ".csv"
        if cd_voltage_finish_flag:
            cd_parameters['voltage_finish_flag'] = True
            if cd_voltage_finish_mode == 0:
                cd_parameters['voltage_finish_mode'] = 0
                cd_parameters['finish_duration'] = int(self.sequence_voltage_finish_time_entry.text())
                cd_parameters['chargecurrent_duration'] = 0
                cd_parameters['dischargecurrent_duration'] = 0
                # print("cd mode 0 - cd_getparams")
                # print(cd_parameters['finish_duration'])
            elif cd_voltage_finish_mode == 1:
                cd_parameters['voltage_finish_mode'] = 1
                cd_parameters['finish_duration'] = 0
                cd_parameters['chargecurrent_duration'] = int(self.sequence_voltage_finish_chargecurrent_entry.text()) / 1e3
                cd_parameters['dischargecurrent_duration'] = int(self.sequence_voltage_finish_dischargecurrent_entry.text()) / 1e3
                # print("cd mode 1 - cd_getparams")
            elif cd_voltage_finish_mode == 2:
                cd_parameters['voltage_finish_mode'] = 2
                cd_parameters['chargecurrent_duration'] = int(self.sequence_voltage_finish_chargecurrent_entry.text()) / 1e3
                cd_parameters['dischargecurrent_duration'] = int(self.sequence_voltage_finish_dischargecurrent_entry.text()) / 1e3
                cd_parameters['finish_duration'] = int(self.sequence_voltage_finish_time_entry.text())
                # print("cd mode 2 - cd_getparams")
        else:
            cd_parameters['voltage_finish_flag'] = False
        cd_voltage_finish_flag = False
        cd_voltage_finish_mode = 0
        return True
    except ValueError:
        QtWidgets.QMessageBox.critical(mainwidget, "Not a number",
                                   "One or more parameters could not be interpreted as a number.")
        return False


def seq_cd_listing(self, listname):
    global cd_parameters
    # seq_cd_getparams(self)
    if seq_cd_getparams(self) and cd_validate_parameters():# and validate_file(cd_parameters['filename'], overwrite_protect=True):
        listname.addItem(cd_parameters['filename'])
        items = listname.findItems(cd_parameters['filename'], QtCore.Qt.MatchExactly)
        if len(items) > 0:
            for item in items:
                i = listname.row(item)
        test_sequence[i] = {}
        test_sequence[i]['test_key'] = i
        test_sequence[i]['test_type'] = 'CCD'
        test_sequence[i].update(cd_parameters)
        self.close()



def seq_rate_getparams(self):
    """Retrieve the rate testing parameters from the GUI input fields and store them in a global dictionary. If succesful, return True."""
    global rate_parameters
    try:
        rate_parameters['lbound'] = float(self.sequence_rate_lbound_entry.text())
        rate_parameters['ubound'] = float(self.sequence_rate_ubound_entry.text())
        rate_parameters['one_c_current'] = float(self.sequence_rate_capacity_entry.text()) / 1e3  # Convert uA to mA
        rate_parameters['crates'] = [float(x) for x in self.sequence_rate_crates_entry.text().split(",")]
        rate_parameters['currents'] = [rate_parameters['one_c_current'] * rc for rc in rate_parameters['crates']]
        rate_parameters['numcycles'] = int(self.sequence_rate_numcycles_entry.text())
        # rate_parameters['numsamples'] = int(self.sequence_rate_numsamples_entry.text())
        rate_parameters['path'] = str(sequence_file_entry.text())
        rate_parameters['name'] = str(self.sequence_rate_file_entry.text())
        rate_parameters['filename'] = rate_parameters['path'] + "/" + rate_parameters['name'] + ".csv"
        # rate_parameters['filename'] = str(sequence_file_entry.text()) + "/" + str(self.sequence_rate_file_entry.text()) + ".csv"
        return True
    except ValueError:
        QtWidgets.QMessageBox.critical(mainwidget, "Not a number",
                                   "One or more parameters could not be interpreted as a number.")
        return False


def seq_rate_listing(self, listname):
    global rate_parameters
    # seq_rate_getparams(self)
    if seq_rate_getparams(self) and rate_validate_parameters():# and validate_file(rate_parameters['filename'], overwrite_protect=True):
        listname.addItem(rate_parameters['filename'])
        items = listname.findItems(rate_parameters['filename'], QtCore.Qt.MatchExactly)
        if len(items) > 0:
            for item in items:
                i = listname.row(item)
        test_sequence[i] = {}
        test_sequence[i]['test_key'] = i
        test_sequence[i]['test_type'] = 'Rate'
        test_sequence[i].update(rate_parameters)
        self.close()



def seq_ocp_listing(self, listname):
    global ocp_parameters
    # seq_ocp_getparams(self)
    if seq_ocp_getparams(self) and ocp_validate_parameters():# and validate_file(ocp_parameters['filename'], overwrite_protect=True):
        listname.addItem(ocp_parameters['filename'])
        items = listname.findItems(ocp_parameters['filename'], QtCore.Qt.MatchExactly)
        if len(items) > 0:
            for item in items:
                i = listname.row(item)
        test_sequence[i] = {}
        test_sequence[i]['test_key'] = i
        test_sequence[i]['test_type'] = 'OCP'
        test_sequence[i].update(ocp_parameters)
        self.close()



def seq_ocp_getparams(self):
    """Retrieve the rate testing parameters from the GUI input fields and store them in a global dictionary. If succesful, return True."""
    global ocp_parameters
    try:
        ocp_parameters['duration'] = int(self.sequence_ocp_duration_entry.text())
        ocp_parameters['numsamples'] = int(self.sequence_ocp_numsamples_entry.text())
        ocp_parameters['path'] = str(sequence_file_entry.text())
        ocp_parameters['name'] = str(self.sequence_ocp_file_entry.text())
        ocp_parameters['filename'] = ocp_parameters['path'] + "/" + ocp_parameters['name'] + ".csv"
        # ocp_parameters['filename'] = str(sequence_file_entry.text()) + "/" + str(self.sequence_ocp_file_entry.text()) + ".csv"
        return True
    except ValueError:
        QtWidgets.QMessageBox.critical(mainwidget, "Not a number",
                                   "One or more parameters could not be interpreted as a number.")
        return False


def seq_skip_test():
    global state
    # NotConnected, Idle_Init, Idle, Measuring_Offset, Stationary_Graph, Measuring_CV, Measuring_CD, Measuring_Rate, Measuring_OCP
    if state == States.Measuring_CV:
        cv_stop(interrupted=True)
    elif state == States.Measuring_CD:
        cd_stop(interrupted=True)
    elif state == States.Measuring_Rate:
        rate_stop(interrupted=True)
    elif state == States.Measuring_OCP:
        ocp_stop(interrupted=True)

def seq_view_list():
    global test_sequence
    # print(test_sequence)
    selected_test = test_sequence[sequence_test_list.currentRow()]
    # print(selected_test)
    MainWindow.update_window(win, selected_test['test_type'])

def seq_stop_all():
    global state, sequence_flag
    sequence_flag = False
    # NotConnected, Idle_Init, Idle, Measuring_Offset, Stationary_Graph, Measuring_CV, Measuring_CD, Measuring_Rate, Measuring_OCP
    if state == States.Measuring_CV:
        cv_stop(interrupted=True)
    elif state == States.Measuring_CD:
        cd_stop(interrupted=True)
    elif state == States.Measuring_Rate:
        rate_stop(interrupted=True)
    elif state == States.Measuring_OCP:
        ocp_stop(interrupted=True)

# def keystoint(x):
#     return {lambda d: int(k) if k.lstrip('-').isdigit() else k: v for k, v in d.items()}
#     # return {int(k): v for k, v in x.items()}

def seq_template_load():
    global sequence_index, sequence_test_list, test_sequence
    sequence_index = 0
    sequence_test_list.clear()
    test_sequence = {}
    filename = sequence_template_file_entry.text()
    # with open('D:/Downloads/pot_test/result.json') as json_file:
    #     test_sequence = json.load(json_file)
    with open(filename) as json_file:
        test_sequence = json.load(json_file, object_hook=lambda d: {int(k)
                         if k.lstrip('-').isdigit() else k: v for k, v in d.items()})
    path = sequence_file_entry.text()
    for test in test_sequence:
        # print(test)
        test_sequence[test]['path'] = path
        test_sequence[test]['filename'] = path + "/" + test_sequence[test]['name'] + ".csv"
        # print(test_sequence[test]['filename'])
        sequence_test_list.addItem(test_sequence[test]['filename'])


def seq_template_save():
    global test_sequence
    filename = sequence_template_file_entry.text()
    # with open('D:/Downloads/pot_test/result.json', 'w') as fp:
    #     json.dump(test_sequence, fp, indent=4, sort_keys=True)
    with open(filename, 'w') as fp:
        json.dump(test_sequence, fp, indent=4, sort_keys=True)


# ------------------------------------------------------------------------------------------
# CV Parameter Pop-up


class SequenceCV(QtWidgets.QWidget):
    def __init__(self):
        global seq_cv_ocv_flag
        seq_cv_ocv_flag = False
        super().__init__()

        cv_msg_box = QtWidgets.QVBoxLayout()
        sequence_vbox.setAlignment(QtCore.Qt.AlignTop)

        sequence_cv_params_box = QtWidgets.QGroupBox(title="Cyclic voltammetry parameters", flat=False)
        format_box_for_parameter(sequence_cv_params_box)
        sequence_cv_params_layout = QtWidgets.QVBoxLayout()
        sequence_cv_params_box.setLayout(sequence_cv_params_layout)
        self.sequence_cv_file_entry = make_label_entry(sequence_cv_params_layout, "Filename (no directory)")
        self.sequence_cv_lbound_entry = make_label_entry(sequence_cv_params_layout, "Lower bound (V)")
        self.sequence_cv_ubound_entry = make_label_entry(sequence_cv_params_layout, "Upper bound (V)")

        sequence_cv_hbox = QtWidgets.QHBoxLayout()
        sequence_cv_label = QtWidgets.QLabel(text="Start potential (V)")
        self.sequence_cv_startpot_entry = QtWidgets.QLineEdit()
        # sequence_cv_get_button = QtGui.QPushButton("OCV")
        # sequence_cv_get_button.setFont(custom_size_font(8))
        # sequence_cv_get_button.setFixedWidth(32)
        # sequence_cv_get_button.clicked.connect(cv_get_ocp)

        self.sequence_cv_ocv_checkbox = QtWidgets.QCheckBox("Start CV at OCV")
        self.sequence_cv_ocv_checkbox.stateChanged.connect(self.seq_toggle_automatic_ocv)
        # sequence_voltage_finish_vbox_layout.addWidget(sequence_cv_ocv_checkbox)

        sequence_cv_hbox.addWidget(sequence_cv_label)
        sequence_cv_hbox.addWidget(self.sequence_cv_startpot_entry)
        # sequence_cv_hbox.addWidget(sequence_cv_get_button)
        sequence_cv_hbox.addWidget(self.sequence_cv_ocv_checkbox)
        sequence_cv_params_layout.addLayout(sequence_cv_hbox)

        self.sequence_cv_stoppot_entry = make_label_entry(sequence_cv_params_layout, "Stop potential (V)")
        self.sequence_cv_scanrate_entry = make_label_entry(sequence_cv_params_layout, "Scan rate (mV/s)")
        self.sequence_cv_scanrate_entry.setToolTip("Maximum Scan Rate: 500mV/s (45mV Step)")
        self.sequence_cv_numcycles_entry = make_label_entry(sequence_cv_params_layout, "Number of cycles")
        self.sequence_cv_numsamples_entry = make_label_entry(sequence_cv_params_layout, "Samples to average")
        self.sequence_cv_numsamples_entry.setToolTip("Time between data points: n x 90E-3 seconds")
        self.sequence_cv_numsamples_entry.setText("1")

        sequence_cv_params_layout.setSpacing(6)
        sequence_cv_params_layout.setContentsMargins(3, 10, 3, 3)
        cv_msg_box.addWidget(sequence_cv_params_box)

        sequence_cv_button_layout = QtWidgets.QHBoxLayout()
        self.sequence_cv_accept_button = QtWidgets.QPushButton("Add")
        self.sequence_cv_accept_button.clicked.connect(
            lambda: seq_cv_listing(win.w, sequence_test_list))
        self.sequence_cv_cancel_button = QtWidgets.QPushButton("Cancel")
        self.sequence_cv_cancel_button.clicked.connect(lambda: self.close())
        sequence_cv_button_layout.addWidget(self.sequence_cv_accept_button)
        sequence_cv_button_layout.addWidget(self.sequence_cv_cancel_button)
        cv_msg_box.addLayout(sequence_cv_button_layout)

        cv_msg_box.setSpacing(6)
        cv_msg_box.setContentsMargins(3, 3, 3, 3)
        self.setLayout(cv_msg_box)

    def seq_toggle_automatic_ocv(self, checkbox_state):
        """Enable or disable constant voltage finishing during constant current tests"""
        global seq_cv_ocv_flag
        if seq_cv_ocv_flag == True:
            seq_cv_ocv_flag = False
            self.sequence_cv_startpot_entry.setEnabled(True)
            # print("CV OCV disabled")
            return
        if seq_cv_ocv_flag == False:
            seq_cv_ocv_flag = True
            self.sequence_cv_startpot_entry.setEnabled(False)
            # print("CV OCV enabled")
            return

    def seq_list_update(self):
        global test_sequence, sequence_flag
        # print("seq_list_update")
        self.sequence_cv_file_entry.setText(test_sequence[sequence_test_list.currentRow()]['name'])
        self.sequence_cv_lbound_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['lbound']))
        self.sequence_cv_ubound_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['ubound']))
        self.sequence_cv_startpot_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['startpot']))
        self.sequence_cv_stoppot_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['stoppot']))
        self.sequence_cv_scanrate_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['scanrate']))
        self.sequence_cv_numcycles_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['numcycles']))
        self.sequence_cv_numsamples_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['numsamples']))
        if test_sequence[sequence_test_list.currentRow()]['auto_ocv'] == True:
            self.sequence_cv_startpot_entry.setEnabled(False)
            self.sequence_cv_ocv_checkbox.setChecked(True)
        self.sequence_cv_accept_button.setText("Update")
        self.sequence_cv_accept_button.clicked.disconnect()
        self.sequence_cv_accept_button.clicked.connect(lambda: self.seq_cv_updateparams())
        if sequence_flag:
            self.sequence_cv_accept_button.setEnabled(False)


    def seq_cv_updateparams(self):
        global test_sequence, cv_parameters, seq_cv_ocv_flag
        if seq_cv_getparams(self) and cv_validate_parameters():
            # print("seq_cv_updateparams")
            # print(test_sequence[sequence_test_list.currentRow()])
            test_sequence[sequence_test_list.currentRow()].update(cv_parameters)
            # print(test_sequence[sequence_test_list.currentRow()])
            # print(test_sequence)
            sequence_test_list.item(sequence_test_list.currentRow()).setText(
                test_sequence[sequence_test_list.currentRow()]["filename"])
            self.close()

# ------------------------------------------------------------------------------------------
# CCD Parameter Pop-up


class SequenceCD(QtWidgets.QWidget):
    def __init__(self):
        super().__init__()
        cd_msg_box = QtWidgets.QVBoxLayout()
        sequence_vbox.setAlignment(QtCore.Qt.AlignTop)

        sequence_cd_params_box = QtWidgets.QGroupBox(title="Charge/discharge parameters", flat=False)
        format_box_for_parameter(sequence_cd_params_box)
        sequence_cd_params_layout = QtWidgets.QVBoxLayout()
        sequence_cd_params_box.setLayout(sequence_cd_params_layout)

        sequence_voltage_finish_vbox = QtWidgets.QGroupBox(title="Voltage finish", flat=False)
        sequence_voltage_finish_vbox_layout = QtWidgets.QVBoxLayout()
        sequence_voltage_finish_vbox.setLayout(sequence_voltage_finish_vbox_layout)

        sequence_voltage_finish_box = QtWidgets.QGroupBox(title="", flat=False)
        sequence_finish_selection_layout = QtWidgets.QHBoxLayout()
        sequence_voltage_finish_box.setLayout(sequence_finish_selection_layout)

        self.sequence_cd_file_entry = make_label_entry(sequence_cd_params_layout, "Filename (no directory)")
        self.sequence_cd_lbound_entry = make_label_entry(sequence_cd_params_layout, "Lower bound (V)")
        self.sequence_cd_ubound_entry = make_label_entry(sequence_cd_params_layout, "Upper bound (V)")
        self.sequence_cd_chargecurrent_entry = make_label_entry(sequence_cd_params_layout, u"Charge current (µA)")
        self.sequence_cd_chargecurrent_entry.setToolTip("Positive -> 1st Cycle Charge / Negative -> 1st Cycle Discharge")
        self.sequence_cd_dischargecurrent_entry = make_label_entry(sequence_cd_params_layout, u"Discharge current (µA)")
        self.sequence_cd_dischargecurrent_entry.setToolTip("Flip sign of the Charge Current")
        self.sequence_cd_numcycles_entry = make_label_entry(sequence_cd_params_layout, "Number of half cycles")
        self.sequence_cd_numsamples_entry = make_label_entry(sequence_cd_params_layout, "Samples to average")
        self.sequence_cd_numsamples_entry.setText("5")

        self.sequence_voltage_finish_time_radio = make_radio_entry(sequence_finish_selection_layout, "Time (s)")
        self.sequence_voltage_finish_time_radio.setChecked(True)
        self.sequence_voltage_finish_time_radio.setEnabled(False)
        self.sequence_voltage_finish_current_radio = make_radio_entry(sequence_finish_selection_layout, "Current (µA)")
        self.sequence_voltage_finish_current_radio.setEnabled(False)
        self.sequence_voltage_finish_both_radio = make_radio_entry(sequence_finish_selection_layout, "Time and current")
        self.sequence_voltage_finish_both_radio.setEnabled(False)
        self.sequence_voltage_finish_time_radio.clicked.connect(lambda: self.seq_set_voltage_finish_mode())
        self.sequence_voltage_finish_current_radio.clicked.connect(lambda: self.seq_set_voltage_finish_mode())
        self.sequence_voltage_finish_both_radio.clicked.connect(lambda: self.seq_set_voltage_finish_mode())

        self.sequence_voltage_finish_checkbox = QtWidgets.QCheckBox("Enable voltage finish")
        self.sequence_voltage_finish_checkbox.stateChanged.connect(self.seq_toggle_voltage_finish)
        sequence_voltage_finish_vbox_layout.addWidget(self.sequence_voltage_finish_checkbox)

        sequence_voltage_finish_vbox_layout.addWidget(sequence_voltage_finish_box)
        self.sequence_voltage_finish_time_entry = make_label_entry(sequence_voltage_finish_vbox_layout, "Time (s)")
        self.sequence_voltage_finish_time_entry.setEnabled(False)
        self.sequence_voltage_finish_chargecurrent_entry = make_label_entry(sequence_voltage_finish_vbox_layout, "Charge Tapering Limit (µA)")
        self.sequence_voltage_finish_chargecurrent_entry.setToolTip("+/- sign must match that in charge current entry")
        self.sequence_voltage_finish_chargecurrent_entry.setEnabled(False)
        self.sequence_voltage_finish_dischargecurrent_entry = make_label_entry(sequence_voltage_finish_vbox_layout,
                                                                 "Discharge Tapering Limit (µA)")
        self.sequence_voltage_finish_dischargecurrent_entry.setToolTip("+/- sign must match that in discharge current entry")
        self.sequence_voltage_finish_dischargecurrent_entry.setEnabled(False)
        sequence_cd_params_layout.addWidget(sequence_voltage_finish_vbox)

        sequence_cd_params_layout.setSpacing(6)
        sequence_cd_params_layout.setContentsMargins(3, 10, 3, 3)
        cd_msg_box.addWidget(sequence_cd_params_box)

        sequence_cd_button_layout = QtWidgets.QHBoxLayout()
        self.sequence_cd_accept_button = QtWidgets.QPushButton("Add")
        self.sequence_cd_accept_button.clicked.connect(
            lambda: seq_cd_listing(win.w, sequence_test_list))
        self.sequence_cd_cancel_button = QtWidgets.QPushButton("Cancel")
        self.sequence_cd_cancel_button.clicked.connect(lambda: self.close())
        sequence_cd_button_layout.addWidget(self.sequence_cd_accept_button)
        sequence_cd_button_layout.addWidget(self.sequence_cd_cancel_button)
        cd_msg_box.addLayout(sequence_cd_button_layout)

        cd_msg_box.setSpacing(6)
        cd_msg_box.setContentsMargins(3, 3, 3, 3)
        self.setLayout(cd_msg_box)

    def seq_list_update(self):
        global test_sequence, sequence_flag
        # print("seq_list_update")
        self.sequence_cd_file_entry.setText(test_sequence[sequence_test_list.currentRow()]['name'])
        self.sequence_cd_lbound_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['lbound']))
        self.sequence_cd_ubound_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['ubound']))
        self.sequence_cd_chargecurrent_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['chargecurrent']*1e3))
        self.sequence_cd_chargecurrent_entry.setToolTip(
            "Positive -> 1st Cycle Charge / Negative -> 1st Cycle Discharge")
        self.sequence_cd_dischargecurrent_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['dischargecurrent']*1e3))
        self.sequence_cd_dischargecurrent_entry.setToolTip("Flip sign of the Charge Current")
        self.sequence_cd_numcycles_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['numcycles']))
        self.sequence_cd_numsamples_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['numsamples']))

        if test_sequence[sequence_test_list.currentRow()]['voltage_finish_flag']:
            self.sequence_voltage_finish_checkbox.setChecked(True)
            self.sequence_voltage_finish_chargecurrent_entry.setEnabled(False)
            self.sequence_voltage_finish_dischargecurrent_entry.setEnabled(False)
            if test_sequence[sequence_test_list.currentRow()]['voltage_finish_mode'] == 0:
                self.sequence_voltage_finish_time_radio
                self.sequence_voltage_finish_time_radio.setChecked(True)
                self.sequence_voltage_finish_current_radio.setChecked(False)
                self.sequence_voltage_finish_both_radio.setChecked(False)
                self.sequence_voltage_finish_time_entry.setEnabled(True)
                self.sequence_voltage_finish_time_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['finish_duration']))
            elif test_sequence[sequence_test_list.currentRow()]['voltage_finish_mode'] == 1:
                self.sequence_voltage_finish_time_radio.setChecked(False)
                self.sequence_voltage_finish_current_radio.setChecked(True)
                self.sequence_voltage_finish_both_radio.setChecked(False)
                self.sequence_voltage_finish_time_entry.setEnabled(False)
                self.sequence_voltage_finish_chargecurrent_entry.setEnabled(True)
                self.sequence_voltage_finish_dischargecurrent_entry.setEnabled(True)
                self.sequence_voltage_finish_chargecurrent_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['chargecurrent_duration']*1e3))
                self.sequence_voltage_finish_dischargecurrent_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['dischargecurrent_duration']*1e3))
            elif test_sequence[sequence_test_list.currentRow()]['voltage_finish_mode'] == 2:
                self.sequence_voltage_finish_time_radio.setChecked(False)
                self.sequence_voltage_finish_current_radio.setChecked(False)
                self.sequence_voltage_finish_both_radio.setChecked(True)
                self.sequence_voltage_finish_time_entry.setEnabled(True)
                self.sequence_voltage_finish_chargecurrent_entry.setEnabled(True)
                self.sequence_voltage_finish_dischargecurrent_entry.setEnabled(True)
                self.sequence_voltage_finish_time_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['finish_duration']))
                self.sequence_voltage_finish_chargecurrent_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['chargecurrent_duration']))
                self.sequence_voltage_finish_dischargecurrent_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['dischargecurrent_duration']))
        self.sequence_cd_accept_button.setText("Update")
        self.sequence_cd_accept_button.clicked.disconnect()
        self.sequence_cd_accept_button.clicked.connect(
            lambda: self.seq_cd_updateparams())
        if sequence_flag:
            self.sequence_cd_accept_button.setEnabled(False)

    def seq_cd_updateparams(self):
        global test_sequence, cd_voltage_finish_flag, cd_voltage_finish_mode, cd_parameters
        if seq_cd_getparams(self) and cd_validate_parameters():
            # print("seq_cd_updateparams")
            # print(test_sequence[sequence_test_list.currentRow()])
            test_sequence[sequence_test_list.currentRow()].update(cd_parameters)
            # print(test_sequence[sequence_test_list.currentRow()])
            # print(test_sequence)
            sequence_test_list.item(sequence_test_list.currentRow()).setText(
                test_sequence[sequence_test_list.currentRow()]["filename"])
            self.close()

    def seq_toggle_voltage_finish(self, checkbox_state):
        """Enable or disable constant voltage finishing during constant current tests"""
        global cd_voltage_finish_flag
        if cd_voltage_finish_flag == True:
            cd_voltage_finish_flag = False
            self.sequence_voltage_finish_time_radio.setEnabled(False)
            self.sequence_voltage_finish_current_radio.setEnabled(False)
            self.sequence_voltage_finish_time_entry.setEnabled(False)
            self.sequence_voltage_finish_chargecurrent_entry.setEnabled(False)
            self.sequence_voltage_finish_dischargecurrent_entry.setEnabled(False)
            self.sequence_voltage_finish_chargecurrent_entry.setText("")
            self.sequence_voltage_finish_dischargecurrent_entry.setText("")
            self.sequence_voltage_finish_time_entry.setText("")
            self.sequence_voltage_finish_both_radio.setEnabled(False)
        if checkbox_state == 2:
            cd_voltage_finish_flag = True
            self.sequence_voltage_finish_time_radio.setEnabled(True)
            self.sequence_voltage_finish_current_radio.setEnabled(True)
            self.sequence_voltage_finish_time_entry.setEnabled(True)
            self.sequence_voltage_finish_time_entry.setText("")
            self.sequence_voltage_finish_both_radio.setEnabled(True)

    def seq_set_voltage_finish_mode(self):
        global cd_voltage_finish_mode
        if self.sequence_voltage_finish_time_radio.isChecked():
            cd_voltage_finish_mode = 0
            # print("voltage finish mode", cd_voltage_finish_mode)
            self.sequence_voltage_finish_time_entry.setText("")
            self.sequence_voltage_finish_chargecurrent_entry.setText("")
            self.sequence_voltage_finish_dischargecurrent_entry.setText("")
            self.sequence_voltage_finish_time_entry.setEnabled(False)
            self.sequence_voltage_finish_time_entry.setEnabled(True)
            self.sequence_voltage_finish_chargecurrent_entry.setEnabled(False)
            self.sequence_voltage_finish_dischargecurrent_entry.setEnabled(False)
        if self.sequence_voltage_finish_current_radio.isChecked():
            cd_voltage_finish_mode = 1
            # print("voltage finish mode", cd_voltage_finish_mode)
            self.sequence_voltage_finish_time_entry.setText("")
            self.sequence_voltage_finish_chargecurrent_entry.setText("")
            self.sequence_voltage_finish_dischargecurrent_entry.setText("")
            self.sequence_voltage_finish_time_entry.setEnabled(False)
            self.sequence_voltage_finish_chargecurrent_entry.setEnabled(False)
            self.sequence_voltage_finish_dischargecurrent_entry.setEnabled(False)
            self.sequence_voltage_finish_chargecurrent_entry.setEnabled(True)
            self.sequence_voltage_finish_dischargecurrent_entry.setEnabled(True)
        if self.sequence_voltage_finish_both_radio.isChecked():
            cd_voltage_finish_mode = 2
            # print("voltage finish mode", cd_voltage_finish_mode)
            # voltage_finish_time_entry.setText("")
            # voltage_finish_current_entry.setText("")
            self.sequence_voltage_finish_time_entry.setEnabled(True)
            self.sequence_voltage_finish_chargecurrent_entry.setEnabled(True)
            self.sequence_voltage_finish_dischargecurrent_entry.setEnabled(True)
        else:
            pass

# ------------------------------------------------------------------------------------------
# Rate Parameter Pop-up


class SequenceRate(QtWidgets.QWidget):
    def __init__(self):
        super().__init__()
        rate_msg_box = QtWidgets.QVBoxLayout()
        sequence_vbox.setAlignment(QtCore.Qt.AlignTop)

        sequence_rate_params_box = QtWidgets.QGroupBox(title="Rate testing parameters", flat=False)
        format_box_for_parameter(sequence_rate_params_box)
        sequence_rate_params_layout = QtWidgets.QVBoxLayout()
        sequence_rate_params_box.setLayout(sequence_rate_params_layout)
        self.sequence_rate_file_entry = make_label_entry(sequence_rate_params_layout, "Filename (no directory)")
        self.sequence_rate_lbound_entry = make_label_entry(sequence_rate_params_layout, "Lower bound (V)")
        self.sequence_rate_ubound_entry = make_label_entry(sequence_rate_params_layout, "Upper bound (V)")
        self.sequence_rate_capacity_entry = make_label_entry(sequence_rate_params_layout, u"C (µAh)")
        self.sequence_rate_crates_entry = make_label_entry(sequence_rate_params_layout, u"C-rates")
        self.sequence_rate_crates_entry.setText("1, 2, 5, 10, 20, 50, 100")
        self.sequence_rate_numcycles_entry = make_label_entry(sequence_rate_params_layout, u"Cycles per C-rate")

        sequence_rate_params_layout.setSpacing(6)
        sequence_rate_params_layout.setContentsMargins(3, 10, 3, 3)
        rate_msg_box.addWidget(sequence_rate_params_box)

        sequence_rate_button_layout = QtWidgets.QHBoxLayout()
        self.sequence_rate_accept_button = QtWidgets.QPushButton("Add")
        self.sequence_rate_accept_button.clicked.connect(
            lambda: seq_rate_listing(win.w, sequence_test_list))
        self.sequence_rate_cancel_button = QtWidgets.QPushButton("Cancel")
        self.sequence_rate_cancel_button.clicked.connect(lambda: self.close())
        sequence_rate_button_layout.addWidget(self.sequence_rate_accept_button)
        sequence_rate_button_layout.addWidget(self.sequence_rate_cancel_button)
        rate_msg_box.addLayout(sequence_rate_button_layout)

        rate_msg_box.setSpacing(6)
        rate_msg_box.setContentsMargins(3, 3, 3, 3)
        self.setLayout(rate_msg_box)

    def seq_list_update(self):
        global test_sequence, sequence_flag
        # print("seq_list_update")
        self.sequence_rate_file_entry.setText(test_sequence[sequence_test_list.currentRow()]['name'])
        self.sequence_rate_lbound_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['lbound']))
        self.sequence_rate_ubound_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['ubound']))
        self.sequence_rate_capacity_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['one_c_current']*1e3))
        self.sequence_rate_crates_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['crates']).replace('[', '').replace(']', ''))
        self.sequence_rate_numcycles_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['numcycles']))
        self.sequence_rate_accept_button.setText("Update")
        self.sequence_rate_accept_button.clicked.disconnect()
        self.sequence_rate_accept_button.clicked.connect(
            lambda: self.seq_rate_updateparams())
        if sequence_flag:
            self.sequence_rate_accept_button.setEnabled(False)

    def seq_rate_updateparams(self):
        global test_sequence, rate_parameters
        if seq_rate_getparams(self) and rate_validate_parameters():
            # print("seq_rate_updateparams")
            # print(test_sequence[sequence_test_list.currentRow()])
            test_sequence[sequence_test_list.currentRow()].update(rate_parameters)
            # print(test_sequence[sequence_test_list.currentRow()])
            # print(test_sequence)
            sequence_test_list.item(sequence_test_list.currentRow()).setText(
                test_sequence[sequence_test_list.currentRow()]["filename"])
            self.close()
# ------------------------------------------------------------------------------------------
# OCV Parameter Pop-up

class SequenceOCP(QtWidgets.QWidget):
    def __init__(self):
        super().__init__()
        ocp_msg_box = QtWidgets.QVBoxLayout()
        sequence_vbox.setAlignment(QtCore.Qt.AlignTop)

        sequence_ocp_params_box = QtWidgets.QGroupBox(title="OCP testing parameters", flat=False)
        format_box_for_parameter(sequence_ocp_params_box)
        sequence_ocp_params_layout = QtWidgets.QVBoxLayout()
        sequence_ocp_params_box.setLayout(sequence_ocp_params_layout)
        self.sequence_ocp_file_entry = make_label_entry(sequence_ocp_params_layout, "Filename (no directory)")
        self.sequence_ocp_duration_entry = make_label_entry(sequence_ocp_params_layout, "Duration (S)")
        self.sequence_ocp_numsamples_entry = make_label_entry(sequence_ocp_params_layout, "Samples to average")
        self.sequence_ocp_numsamples_entry.setText("5")
        sequence_ocp_params_layout.setSpacing(6)
        sequence_ocp_params_layout.setContentsMargins(3, 10, 3, 3)
        ocp_msg_box.addWidget(sequence_ocp_params_box)

        sequence_ocp_button_layout = QtWidgets.QHBoxLayout()
        self.sequence_ocp_accept_button = QtWidgets.QPushButton("Add")
        self.sequence_ocp_accept_button.clicked.connect(
            lambda: seq_ocp_listing(win.w, sequence_test_list))
        self.sequence_ocp_cancel_button = QtWidgets.QPushButton("Cancel")
        self.sequence_ocp_cancel_button.clicked.connect(lambda: self.close())
        sequence_ocp_button_layout.addWidget(self.sequence_ocp_accept_button)
        sequence_ocp_button_layout.addWidget(self.sequence_ocp_cancel_button)
        ocp_msg_box.addLayout(sequence_ocp_button_layout)

        ocp_msg_box.setSpacing(6)
        ocp_msg_box.setContentsMargins(3, 3, 3, 3)
        self.setLayout(ocp_msg_box)

    def seq_list_update(self):
        global test_sequence, sequence_flag
        # print("seq_list_update")
        self.sequence_ocp_file_entry.setText(test_sequence[sequence_test_list.currentRow()]['name'])
        self.sequence_ocp_duration_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['duration']))
        self.sequence_ocp_numsamples_entry.setText(str(test_sequence[sequence_test_list.currentRow()]['numsamples']))
        self.sequence_ocp_accept_button.setText("Update")
        self.sequence_ocp_accept_button.clicked.disconnect()
        self.sequence_ocp_accept_button.clicked.connect(
            lambda: self.seq_ocp_updateparams())
        if sequence_flag:
            self.sequence_ocp_accept_button.setEnabled(False)

    def seq_ocp_updateparams(self):
        global test_sequence, ocp_parameters
        if seq_ocp_getparams(self):
            # print("seq_ocp_updateparams")
            # print(test_sequence[sequence_test_list.currentRow()])
            test_sequence[sequence_test_list.currentRow()].update(ocp_parameters)
            # print(test_sequence[sequence_test_list.currentRow()])
            # print(test_sequence)
            sequence_test_list.item(sequence_test_list.currentRow()).setText(
                test_sequence[sequence_test_list.currentRow()]["filename"])
            self.close()
# ------------------------------------------------------------------------------------------
hbox = QtWidgets.QHBoxLayout()
hbox.addLayout(display_plot_frame)
hbox.addWidget(tab_frame)

vbox = QtWidgets.QVBoxLayout()
statustext = QtWidgets.QPlainTextEdit()
statustext.setFixedHeight(90)
vbox.addLayout(hbox)
vbox.addWidget(statustext)

mainwidget = QtWidgets.QWidget()
win.setCentralWidget(mainwidget)
vbox.setContentsMargins(0, 0, 0, 0)
mainwidget.setLayout(vbox)


# main program body ----------------------------------------------------------------------------------------------------

def periodic_update():  # A state machine is used to determine which functions need to be called, depending on the current state of the program
    global sequence_flag, state
    if state == States.Idle_Init:
        idle_init()
    elif state == States.Idle:
        read_potential_current()
        update_live_graph()
    elif state == States.Sequence_Idle:
        sequence_start()
    elif state == States.Measuring_CV:
        cv_update()
    elif state == States.Measuring_CD:
        cd_update()
    elif state == States.Measuring_Rate:
        rate_update()
    elif state == States.Measuring_OCP:
        ocp_update()
    elif state == States.Measuring_Temp:
        update_temp_measurement()
    elif state == States.Stationary_Graph:
        read_potential_current()


# ----------------------------------------------------------------------------------------------------------------------
if usb_debug_flag:
    '''Depending on global flag, toggles debugging of USB features. Setting this up to help diagnose crashes during longer CV tests.
    This logging method does not rotate files due to the long run times of our tests, and because the errors flood the output streams
    This means that log files can reach several GIGABYTES IN SIZE. Word processors can only open files under 500MB, so it is necessary
    to split the file. This is easiest in Linux's command line ->
    split -b 200MB filepath
    this will split the file (located at filepath) into as many 200MB chunks as necessary'''

    file_path = os.getcwd()
    os.environ['PYUSB_DEBUG'] = 'debug'
    pyusb_path = 'pyusb_log.log'
    os.environ['LIBUSB_DEBUG'] = '3'
    log_path = os.path.join(file_path, 'cv_log.log')
    logging.basicConfig(
        level=logging.DEBUG,
        format='%(asctime)s:%(levelname)s:%(name)s:%(message)s',
        filename=log_path,
        filemode='a'
    )
    stdout_logger = logging.getLogger('STDOUT')
    sl = StreamToLogger(stdout_logger, logging.DEBUG)
    sys.stdout = sl

    stderr_logger = logging.getLogger('STDERR')
    sl = StreamToLogger(stderr_logger, logging.ERROR)
    sys.stderr = sl
# ---------------------------------------------------------------------------------------------------------------------

timer = QtCore.QTimer()
timer.timeout.connect(periodic_update)
timer.start(
    int(qt_timer_period))  # Calls periodic_update() every adcread_interval (as defined in the beginning of this program)

log_message("Program started. Press the \"Connect\" button in the hardware tab to connect to the USB interface.")

win.show()  # Show the main window
sys.exit(
    app.exec_())  # Keep the program running by periodically calling the periodic_update() until the GUI window is closed
