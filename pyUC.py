#!/usr/bin/python3
###################################################################################
# pyUC ("puck")
# Copyright (C) 2014, 2015, 2016, 2019, 2020 N4IRR
#
# This software is for use on amateur radio networks only, it is to be used
# for educational purposes only. Its use on commercial networks is strictly 
# prohibited.  Permission to use, copy, modify, and/or distribute this software 
# hereby granted, provided that the above copyright notice and this permission 
# notice appear in all copies.
#
# THE SOFTWARE IS PROVIDED "AS IS" AND DVSWITCH DISCLAIMS ALL WARRANTIES WITH
# REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
# AND FITNESS.  IN NO EVENT SHALL N4IRR BE LIABLE FOR ANY SPECIAL, DIRECT,
# INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
# LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE
# OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
# PERFORMANCE OF THIS SOFTWARE.
###################################################################################

from tkinter import *
from tkinter import ttk
from time import time, sleep, localtime, strftime
from random import randint
import socket
import struct
import _thread
import shlex
import configparser, traceback
import pyaudio
import audioop
import json
import logging
import os
import io
import base64
import urllib.request
import queue
from pathlib import Path
import hashlib
from tkinter import font
import sys
import zmq
import pmt

###################################################################################
# Declare input and output ports for communication with AB
###################################################################################
usrp_tx_port = 50002
usrp_rx_port = 50001

###################################################################################
# USRP packet types
###################################################################################
USRP_TYPE_VOICE = 0
USRP_TYPE_DTMF = 1
USRP_TYPE_TEXT = 2
USRP_TYPE_PING = 3
USRP_TYPE_TLV = 4
USRP_TYPE_VOICE_ADPCM = 5
USRP_TYPE_VOICE_ULAW = 6

###################################################################################
# TLV tags
###################################################################################
TLV_TAG_BEGIN_TX    = 0
TLV_TAG_AMBE        = 1
TLV_TAG_END_TX      = 2
TLV_TAG_TG_TUNE     = 3
TLV_TAG_PLAY_AMBE   = 4
TLV_TAG_REMOTE_CMD  = 5
TLV_TAG_AMBE_49     = 6
TLV_TAG_AMBE_72     = 7
TLV_TAG_SET_INFO    = 8
TLV_TAG_IMBE        = 9
TLV_TAG_DSAMBE      = 10
TLV_TAG_FILE_XFER   = 11

###################################################################################
# Globals (gah)
###################################################################################
noTrace = False                     # Boolean to control recursion when a new mode is selected
usrpSeq = 0                         # Each USRP packet has a unique sequence number
udp = None                          # UDP socket for USRP traffic
out_index = None                    # Current output (speaker) index in the pyaudio device list
in_index = None                     # Current input (mic) index in the pyaudio device list
regState = False                    # Global registration state boolean
noQuote = {ord('"'): ''}
SAMPLE_RATE = 48000                 # Default audio sample rate for pyaudio (will be resampled to 8K)
toast_frame = None                  # A toplevel window used to display toast messages
ipc_queue = None                    # Queue used to pass info to main hread (UI)
ptt = False                         # Current ptt state
tx_start_time = 0                   # TX timer
done = False                        # Thread stop flag
transmit_enable = True              # Make sure that UC is half duplex
level_every_sample = 1
NAT_ping_timer = 0

transmitButton = None               # tk object
logList = None                      # tk object
macros = {}

uc_background_color = "gray25"
uc_text_color = "white"

###################################################################################
# Strings
###################################################################################
STRING_USRP_CLIENT = "USRP Client"
STRING_FATAL_ERROR = "fatal error, python package not found: "
STRING_OK = "OK"
STRING_REGISTERED =  "Registered"
STRING_WINDOWS_PORT_REUSE = "On Windows, ignore the port reuse"
STRING_FATAL_OUTPUT_STREAM = "fatal error, can not open output audio stream"
STRING_OUTPUT_STREAM_ERROR = "Output stream  open error"
STRING_FATAL_INPUT_STREAM = "fatal error, can not open input audio stream"
STRING_INPUT_STREAM_ERROR = "Input stream  open error"
STRING_CONNECTION_FAILURE = "Connection failure"
STRING_SOCKET_FAILURE = "Socket failure"
STRING_CONNECTED_TO = "Connected to"
STRING_DISCONNECTED = "Disconnected "
STRING_SERVER = "Server"
STRING_READ = "Read"
STRING_WRITE = "Write"
STRING_AUDIO = "Audio"
STRING_MIC = "Mic"
STRING_SPEAKER = "Speaker"
STRING_INPUT = "Input"
STRING_OUTPUT = "Output"
STRING_TG = "TG"
STRING_TS = "TS"
STRING_CONNECT = "Connect"
STRING_DISCONNECT = "Disconnect"
STRING_DATE = "Date"
STRING_TIME = "Time"
STRING_CALL = "Call"
STRING_LOSS = "Loss"
STRING_DURATION = "Duration"
STRING_MODE = "MODE"
STRING_REPEATER_ID = "Repeater ID"
STRING_SUBSCRIBER_ID = "Subscriber ID"
STRING_TAB_MAIN = "Main"
STRING_TAB_SETTINGS = "Settings"
STRING_TAB_ABOUT = "About"
STRING_CONFIG_NOT_EDITED = 'Please edit the configuration file and set it up correctly. Exiting...'
STRING_CONFIG_FILE_ERROR = "Config (ini) file error: "
STRING_EXITING = "Exiting pyUC..."
STRING_VOX = "Vox"
STRING_DONGLE_MODE = "Dongle Mode"
STRING_VOX_ENABLE = "Vox Enable"
STRING_VOX_THRESHOLD = "Threshold"
STRING_VOX_DELAY = "Delay"
STRING_NETWORK = "Network"
STRING_LOOPBACK = "Loopback"
STRING_IP_ADDRESS = "IP Address"
STRING_PRIVATE = "Private"
STRING_GROUP = "Group"
STRING_TRANSMIT = "Transmit"

###################################################################################
# HTML/QRZ import libraries
try:
    from urllib.request import urlopen
    from bs4 import BeautifulSoup
    from PIL import Image, ImageTk
    import requests
except:
    print(STRING_FATAL_ERROR + str(sys.exc_info()[1]))
    exit(1)

###################################################################################
def ping_thread():
    while done == False:
        sleep(20.0)
        sendUSRPCommand(bytes("PING", 'ASCII'), USRP_TYPE_PING)

###################################################################################
# Log output to console
###################################################################################
logging.basicConfig(format='%(asctime)s - %(message)s', level=logging.INFO)

###################################################################################
# Open the UDP socket for TX and RX
###################################################################################
def openStream():
    global usrpSeq
    global udp

    usrpSeq = 0
    udp = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        udp.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEPORT, 1)
    except:
        logging.info(STRING_WINDOWS_PORT_REUSE)
        pass
    if (usrp_rx_port in usrp_tx_port) == False:    # single  port reply does not need a bind
        logging.info("Listening on port %d", usrp_rx_port)
        udp.bind(('', usrp_rx_port))

def sendto(usrp):
    for port in usrp_tx_port:
        udp.sendto(usrp, (ip_address, port))

from ctypes import *
from contextlib import contextmanager

ERROR_HANDLER_FUNC = CFUNCTYPE(None, c_char_p, c_int, c_char_p, c_int, c_char_p)

def py_error_handler(filename, line, function, err, fmt):
    pass

c_error_handler = ERROR_HANDLER_FUNC(py_error_handler)

@contextmanager
def noalsaerr():
    try:
        asound = cdll.LoadLibrary('libasound.so')
        asound.snd_lib_error_set_handler(c_error_handler)
        yield
        asound.snd_lib_error_set_handler(None)
    except:
        yield
        pass

###################################################################################
# Log the EOT
###################################################################################
def log_end_of_transmission(call,rxslot,tg,loss,start_time):
    logging.info('End TX:   {} {} {} {} {:.2f}s'.format(call, rxslot, tg, loss, time() - start_time))

###################################################################################
# RX thread, collect audio and metadata from AB
###################################################################################
def rxAudioStream():
    global ip_address
    global noTrace
    global regState
    global transmit_enable
    global macros

    logging.info('Start rx audio thread')
    USRP = bytes("USRP", 'ASCII')
    REG = bytes("REG:", 'ASCII')
    UNREG = bytes("UNREG", 'ASCII')
    OK = bytes("OK", 'ASCII')
    INFO = bytes("INFO:", 'ASCII')
    EXITING = bytes("EXITING", 'ASCII')

    FORMAT = pyaudio.paInt16
    CHUNK = 160 if SAMPLE_RATE == 8000 else (160*6)     # Size of chunk to read
    CHANNELS = 1
    RATE = SAMPLE_RATE
    
    try:
        stream = p.open(format=FORMAT,
                        channels = CHANNELS,
                        rate = RATE,
                        output = True,
                        frames_per_buffer = CHUNK,
                        output_device_index=out_index
                        )
    except:
        logging.critical(STRING_FATAL_OUTPUT_STREAM + str(sys.exc_info()[1]))
        os._exit(1)

    _i = p.get_default_output_device_info().get('index') if out_index == None else out_index
    logging.info("Output Device: {} Index: {}".format(p.get_device_info_by_host_api_device_index(0, _i).get('name'), _i))

    lastKey = -1
    start_time = time()
    call = ''
    name = ''
    tg = ''
    lastSeq = 0
    seq = 0
    loss = '0.00%'
    rxslot = '0'
    state = None
    
    while done == False:
        soundData, addr = udp.recvfrom(1024)
        if (addr[0] != ip_address):
            ip_address = addr[0] # OK, this was supposed to help set the ip to a server, but multiple servers ping/pong.  I may remove it.
        if (soundData[0:4] == USRP):
            eye = soundData[0:4]
            seq, = struct.unpack(">i", soundData[4:8])
            memory, = struct.unpack(">i", soundData[8:12])
            keyup, = struct.unpack(">i", soundData[12:16])
            type, = struct.unpack("i", soundData[20:24])
            mpxid, = struct.unpack(">i", soundData[24:28])
            reserved, = struct.unpack(">i", soundData[28:32])
            audio = soundData[32:]
            if (type == USRP_TYPE_VOICE): # voice
                audio = soundData[32:]

                print(eye, seq, keyup, memory, type, mpxid, reserved, len(audio), len(soundData), RATE)

                if (len(audio) == 320):
                    if RATE == 48000:
                        (audio48, state) = audioop.ratecv(audio, 2, 1, 8000, 48000, state)
                        rep_sock.sendto(audio, ("10.0.1.200", 50003))
                        stream.write(bytes(audio48), CHUNK)
                        if (seq % level_every_sample) == 0:
                            rms = audioop.rms(audio, 2)     # Get a relative power value for the sample
                            audio_level = int(rms/100)
                    else:
                        stream.write(audio, CHUNK)
                if (keyup != lastKey):
                    logging.debug('key' if keyup else 'unkey')
                    if keyup:
                        start_time = time()
                    if keyup == False:
                        log_end_of_transmission(call, rxslot, tg, loss, start_time)
                        transmit_enable = True  # Idle state, allow local transmit
                        audio_level = 0
                lastKey = keyup
            elif (type == USRP_TYPE_TEXT): #metadata
                if (audio[0:4] == REG):
                    if (audio[4:9] == UNREG):
                        disconnect()
                        regState = False
                        pass
                    elif (audio[4:11] == EXITING):
                        disconnect()
                        tmp = audio[:audio.find(b'\x00')].decode('ASCII') # C string
                        args = tmp.split(" ")
                        sleepTime = int(args[2])
                        logging.info("AB is exiting and wants a re-reg in %s seconds...", sleepTime)
                        if (sleepTime > 0):
                            sleep(sleepTime)
                            registerWithAB()
                    logging.info(audio[:audio.find(b'\x00')].decode('ASCII'))
                elif (audio[0:5] == INFO):
                    _json = audio[5:audio.find(b'\x00')].decode('ASCII')
                    if (_json[0:4] == "MSG:"):
                        logging.info("Text Message: " + _json[4:])
                    elif (_json[0:6] == "MACRO:"):  # An ad-hoc macro menu
                        logging.info("Macro: " + _json[6:])
                        macs = _json[6:]
                        macrosx = dict(x.split(",") for x in macs.split("|"))
                        macros = { k:v.strip() for k, v in macrosx.items()}
                    elif (_json[0:5] == "MENU:"):  # An ad-hoc macro menu
                        logging.info("Menu: " + _json[5:])
                        macs = _json[5:]
                        macrosx = dict(x.split(",") for x in macs.split("|"))
                        macros = { k:v.strip() for k, v in macrosx.items()}
                else:
                    # Tunnel a TLV inside of a USRP packet
                    if audio[0] == TLV_TAG_SET_INFO:
                        transmit_enable = False # Transmission from network will disable local transmit
            elif (type == USRP_TYPE_PING):
                if transmit_enable == False:    # Do we think we receiving packets?, lets test for EOT missed
                    if (lastSeq+1) == seq:
                        logging.info("missed EOT")
                        log_end_of_transmission(call, rxslot, tg, loss, start_time)
                        transmit_enable = True  # Idle state, allow local transmit
                    lastSeq = seq
#                logging.debug(audio[:audio.find('\x00')])
                pass
            elif (type == USRP_TYPE_TLV):
                tag = audio[0]
                length = audio[1]
                value = audio[2:]    
                if tag == TLV_TAG_FILE_XFER:
                    FILE_SUBCOMMAND_NAME = 0
                    FILE_SUBCOMMAND_PAYLOAD = 1
                    FILE_SUBCOMMAND_WRITE = 2
                    FILE_SUBCOMMAND_READ = 3
                    FILE_SUBCOMMAND_ERROR = 4
                    if value[0] == FILE_SUBCOMMAND_NAME:
                        file_len = (value[1] << 24) + (value[2] << 16) + (value[3] << 8) + value[4]
                        file_name = value[5:]
                        zero = file_name.find(0)
                        file_name = file_name[:zero].decode('ASCII')
                        logging.info("File transfer name: " + file_name)
                        m = hashlib.md5()
                    if value[0] == FILE_SUBCOMMAND_PAYLOAD:
                        logging.debug("payload len = " + str(length-1))
                        payload = value[1:length]
                        m.update(payload)
                        #logging.debug(payload.hex())
                        #logging.debug(payload)
                    if value[0] == FILE_SUBCOMMAND_WRITE:
                        digest = m.digest().hex().upper()
                        file_md5 = value[1:33].decode('ASCII')
                        if (digest == file_md5):
                            logging.info("File digest matches")
                        else:
                            logging.info("File digest does not match {} vs {}".format(digest, file_md5))
                        #logging.info("write (md5): " + value[1:33].hex())
                    if value[0] == FILE_SUBCOMMAND_ERROR:
                        logging.info("error")
        else:
#            logging.info(soundData, len(soundData))
            pass

#    udp.close()

###################################################################################
# TX thread, send audio to AB
###################################################################################
def txAudioStream():
    global usrpSeq
    global ptt
    global transmit_enable
    FORMAT = pyaudio.paInt16                            # 16 bit signed ints
    CHUNK = 160 if SAMPLE_RATE == 8000 else (160*6)     # Size of chunk to read
    CHANNELS = 1                                        # mono
    RATE = SAMPLE_RATE
    state = None                                        # resample state between fragments
    
    try:
        stream = p.open(format=FORMAT,
                        channels = CHANNELS,
                        rate = RATE,
                        input = True,
                        frames_per_buffer = CHUNK,
                        input_device_index=in_index
                        )
    except:
        logging.critical(STRING_FATAL_INPUT_STREAM + str(sys.exc_info()[1]))
        transmit_enable = False
        return

    _i = p.get_default_output_device_info().get('index') if in_index == None else in_index
    logging.info("Input Device: {} Index: {}".format(p.get_device_info_by_host_api_device_index(0, _i).get('name'), _i))

    lastPtt = ptt
    while done == False:
        try:

            if RATE == 48000:       # If we are reading at 48K we need to resample to 8K
                audio48 = stream.read(CHUNK, exception_on_overflow=False)
                (audio, state) = audioop.ratecv(audio48, 2, 1, 48000, 8000, state)
            else:
                audio = stream.read(CHUNK, exception_on_overflow=False)

            rms = audioop.rms(audio, 2)     # Get a relative power value for the sample
            ###### Vox processing #####
            # if vox_enable.get():
            #     if rms > vox_threshold.get():   # is it loud enough?
            #         decay = vox_delay.get()     # Yes, reset the decay value (wont unkey for N samples)
            #         if (ptt == False) and (transmit_enable == True):            # Are we changing ptt state to True?
            #             ptt = True              # Set it
            #             showPTTState(0)         # Update the UI (turn transmit button red, etc)
            #     elif ptt == True:               # Are we too soft and transmitting?
            #         decay -= 1                  # Decrement the decay counter
            #         if decay <= 0:              # Have we passed N samples, all of them less then the threshold?
            #             ptt = False             # Unkey
            #             showPTTState(1)         # Update the UI
            ###########################
            if ptt != lastPtt:
                usrp = 'USRP'.encode('ASCII') + struct.pack('>iiiiiii',usrpSeq, 0, ptt, 0, USRP_TYPE_VOICE, 0, 0) + audio
                sendto(usrp)
                usrpSeq = usrpSeq + 1
            lastPtt = ptt
            if ptt:
                usrp = 'USRP'.encode('ASCII') + struct.pack('>iiiiiii',usrpSeq, 0, ptt, 0, USRP_TYPE_VOICE, 0, 0) + audio
                # logging.warning(len(audio))
                sendto(usrp)
                usrpSeq = usrpSeq + 1
                audio_level = int(rms/100)
        except:
            logging.warning("TX thread:" + str(sys.exc_info()[1]))

def debugAudio():
    p = pyaudio.PyAudio()
    info = p.get_host_api_info_by_index(0)
    print("------------------------------------")
    print("Info: ", info)
    print("------------------------------------")
    numdevices = info.get('deviceCount')
    for i in range(0, numdevices):
        if (p.get_device_info_by_host_api_device_index(0, i).get('maxInputChannels')) > 0:
            print("Input Device id ", i, " - ", p.get_device_info_by_host_api_device_index(0, i).get('name'))
        print("Device: ", p.get_device_info_by_host_api_device_index(0, i))
        print("===============================")
    print("Output: ", p.get_default_output_device_info())
    print("Input: ", p.get_default_input_device_info())

def listAudioDevices(want_input):
    devices = []
    p = pyaudio.PyAudio()
    info = p.get_host_api_info_by_index(0)
    numdevices = info.get('deviceCount')
    for i in range(0, numdevices):
        is_input = p.get_device_info_by_host_api_device_index(0, i).get('maxInputChannels') > 0
        if (is_input and want_input) or (want_input == False and is_input == False):
            devices.append(p.get_device_info_by_host_api_device_index(0, i).get('name'))
            logging.info("Device id {} - {}".format(i, p.get_device_info_by_host_api_device_index(0, i).get('name')))
    return devices

debugAudio()
#exit(1)

###################################################################################
# Catch and display any socket errors
###################################################################################
def socketFailure():
    logging.error(STRING_SOCKET_FAILURE)

###################################################################################
# Send command to AB
###################################################################################
def sendUSRPCommand( cmd, packetType ):
    global usrpSeq
    logging.info("sendUSRPCommand: "+ str(cmd))
    try:
        # Send "text" packet to AB. 
        usrp = 'USRP'.encode('ASCII') + (struct.pack('>iiiiiii',usrpSeq, 0, 0, 0, packetType << 24, 0, 0)) + cmd
        usrpSeq = (usrpSeq + 1) & 0xffff
        sendto(usrp)
    except:
        traceback.print_exc()
        socketFailure()

###################################################################################
# Send command to AB
###################################################################################
def sendRemoteControlCommand( cmd ):
    logging.info("sendRemoteControlCommand: "+ str(cmd))
    # Use TLV to send command (wrapped in a USRP packet). 
    tlv = struct.pack("BB", TLV_TAG_REMOTE_CMD, len(cmd))[0:2] + cmd
    sendUSRPCommand(tlv, USRP_TYPE_TLV)

def sendRemoteControlCommandASCII( cmd ):
    sendRemoteControlCommand(bytes(cmd, 'ASCII'))
###################################################################################
# Send command to DMRGateway
###################################################################################
def sendToGateway( cmd ):
    logging.info("sendToGateway: " + cmd)

###################################################################################
# Request the INFO json from AB
###################################################################################
def requestInfo():
    sendUSRPCommand(bytes("INFO:", 'ASCII'), USRP_TYPE_TEXT)

###################################################################################
# Set the size (number of bits) of each AMBE sample
###################################################################################
def setAMBESize(size):
    sendRemoteControlCommandASCII("ambeSize="+size)

###################################################################################
# Set the AMBE mode to DMR|DSTAR|YSF|NXDN|P25
###################################################################################
def setAMBEMode(mode):
    sendRemoteControlCommandASCII("ambeMode="+mode)

###################################################################################
# 
###################################################################################
def getInfo():
    logging.info("getInfo")

###################################################################################
# xx_Bridge command: section
###################################################################################
def setRemoteNetwork( netName ):
    logging.info("setRemoteNetwork")

###################################################################################
# Set the AB mode by running the named macro
###################################################################################
def setMode( mode ):
    sendUSRPCommand(bytes("*" + mode, 'ASCII'), USRP_TYPE_DTMF)

###################################################################################
#
###################################################################################
def setVoxData():
    return
    # v = "true" if vox_enable.get() > 0 else "false"
    # sendToGateway("set vox " + v)
    # sendToGateway("set vox_threshold " + str(vox_threshold.get()))
    # sendToGateway("set vox_delay " + str(vox_delay.get()))

###################################################################################
#
###################################################################################
def getVoxData():
    return
    # sendToGateway("get vox")
    # sendToGateway("get vox_threshold ")
    # sendToGateway("get vox_delay ")

###################################################################################
#
###################################################################################
def setAudioData():
    return
    # dm = "true" if dongle_mode.get() > 0 else "false"
    # sendToGateway("set dongle_mode " + dm)
    # sendToGateway("set sp_level " + str(sp_vol.get()))
    # sendToGateway("set mic_level " + str(mic_vol.get()))

###################################################################################
# Connect to a specific set of TS/TG values
###################################################################################
def connect(tup):
    start()

###################################################################################
# Mute all TS/TGs
###################################################################################
def disconnect():
    logging.info("Disconnected")
#    transmitButton.configure(state='disabled')

###################################################################################
#
###################################################################################
def start():
    global regState
    regState = True

###################################################################################
# Combined command to get all values from servers and display them on UI
###################################################################################
def getValuesFromServer():
    #   ip_address.set("127.0.0.1")
    #   loopback.set(1)

    # get values from Analog_Bridge (repeater ID, Sub ID, master, tg, slot)
    ### Old Command ### sendRemoteControlCommand('get_info')
    sendToGateway('get info')
    
    # get values from Analog_Bridge (vox enable, delay and threshold) (not yet: sp level, mic level, audio devices)
    # getVoxData()                        #vox enable, delay and threshold
    # dongle_mode.set(1)                   #dongle mode enable
    # mic_vol.set(50)                      #microphone level
    # sp_vol.set(50)                       #speaker level

###################################################################################
# Update server data state to match GUI values
###################################################################################
def sendValuesToServer():
    setVoxData()                        #vox enable, delay and threshold
    setAudioData()                      #sp level, mic level, dongle mode

###################################################################################
# Toggle PTT and display new state
###################################################################################
def transmit():
    global ptt
    
    if (transmit_enable == False) and (ptt == False):  # Do not allow transmit key if rx is active
        return

    ptt = not ptt
    if ptt:
        showPTTState(0)
    else:
        showPTTState(1)

###################################################################################
# Update UI with PTT state.
###################################################################################
def showPTTState(flag):
    global tx_start_time
    if ptt:
        tx_start_time = time()
        logging.info("PTT ON")
    else:
        if flag == 1:
            _date = strftime("%m/%d/%y", localtime(time()))
            _time = strftime("%H:%M:%S", localtime(time()))
            _duration = '{:.2f}'.format(time() - tx_start_time)
        logging.info("PTT OFF")

###################################################################################
# Used for debug
###################################################################################
def cb(value):
    logging.info("value = %s", value.get())

###################################################################################
def update_clock(obj):
    now = strftime("%H:%M:%S")
    obj.configure(text=now)

###################################################################################
# Read an int value from the ini file.  If an error or value is Default, return the 
# valDefault passed in.
###################################################################################
def readValue( config, stanza, valName, valDefault, func ):
    try:
        val = config.get(stanza, valName).split(None)[0]
        if val.lower() == "default":  # This is a special case for the in and out index settings
            return valDefault
        return func(val)
    except:
        return valDefault

###################################################################################
# Close down the app when the main window closes.  Signal the threads to terminate
# and tell AB we are done.
###################################################################################
def on_closing():
    global done
    logging.info(STRING_EXITING)
    done = True             # Signal the threads to terminate

############################################################################################################
# Global commands
############################################################################################################

# Load data from the config file
if len(sys.argv) > 1:
    config_file_name = sys.argv[1]      # Use the command line argument for the path to the config file
else:
    config_file_name = str(Path(sys.argv[0]).parent) + "/pyUC.ini"       # Use the default config file name in the same dir as .py file

config = configparser.ConfigParser(inline_comment_prefixes=(';',))
config.optionxform = lambda option: option

try:
    config.read(config_file_name)
    ip_address = config.get('DEFAULTS', "ipAddress").split(None)[0]
    usrp_tx_port = [int(i) for i in config.get('DEFAULTS', "usrpTxPort").split(',')]
    usrp_rx_port = int(config.get('DEFAULTS', "usrpRxPort").split(None)[0])
    level_every_sample = int(readValue(config, 'DEFAULTS', 'levelEverySample', 2, int))
    NAT_ping_timer = int(readValue(config, 'DEFAULTS', 'pingTimer', 0, int))

    in_index = readValue(config, 'DEFAULTS', 'in_index', None, int)
    out_index = readValue(config, 'DEFAULTS', 'out_index', None, int)

except:
    logging.error(STRING_CONFIG_FILE_ERROR + str(sys.exc_info()[1]))
    sys.exit('Configuration file \''+config_file_name+'\' is not a valid configuration file! Exiting...')

audio_level = int(0)

openStream()    # Open the UDP stream to AB
with noalsaerr():
    p = pyaudio.PyAudio()
_thread.start_new_thread( rxAudioStream, () )
if in_index != -1:  # Do not launch the TX thread if the user wants RX only access
    _thread.start_new_thread( txAudioStream, () )
if NAT_ping_timer > 0:
    _thread.start_new_thread( ping_thread, () )

disconnect()    # Start out in the disconnected state
start()         # Begin the handshake with AB (register)

# create a REP socket
_PROTOCOL = "tcp://"
_SERVER = "0.0.0.0"          # localhost
_REP_PORT = ":50003"
_REP_ADDR = _PROTOCOL + _SERVER + _REP_PORT
_debug = 1

#zmq.COPY_THRESHOLD = 320

#if (_debug):
#    print ("'zmq_REQ_REP_server' version 20056.1 binding to:", _REP_ADDR)
#rep_context = zmq.Context()
#if (_debug):
#   assert (rep_context)
#rep_sock = rep_context.socket (zmq.PUB)
#if (_debug):
#    assert (rep_sock)
#rc = rep_sock.bind (_REP_ADDR)

rep_sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
rep_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEPORT, 1)

while done == False:
    # Main thread sleep
    sleep(1)
