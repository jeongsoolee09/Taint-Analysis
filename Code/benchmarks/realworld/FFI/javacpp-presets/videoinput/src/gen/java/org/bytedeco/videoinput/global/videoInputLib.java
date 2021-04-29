// Targeted by JavaCPP version 1.5.4: DO NOT EDIT THIS FILE

package org.bytedeco.videoinput.global;

import org.bytedeco.videoinput.*;

import java.nio.*;
import org.bytedeco.javacpp.*;
import org.bytedeco.javacpp.annotation.*;

import static org.bytedeco.javacpp.presets.javacpp.*;

public class videoInputLib extends org.bytedeco.videoinput.presets.videoInputLib {
    static { Loader.load(); }

// Targeting ..\StringVector.java


// Parsed from <videoInput.h>

// #ifndef _VIDEOINPUT
// #define _VIDEOINPUT

//THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
//OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
//THE SOFTWARE.

//////////////////////////////////////////////////////////
//Written by Theodore Watson - theo.watson@gmail.com    //
//Do whatever you want with this code but if you find   //
//a bug or make an improvement I would love to know!    //
//														//
//Warning This code is experimental 					//
//use at your own risk :)								//
//////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////
/*                     Shoutouts

Thanks to:

		   Dillip Kumar Kara for crossbar code.
		   Zachary Lieberman for getting me into this stuff
		   and for being so generous with time and code.
		   The guys at Potion Design for helping me with VC++
		   Josh Fisher for being a serious C++ nerd :)
		   Golan Levin for helping me debug the strangest
		   and slowest bug in the world!

		   And all the people using this library who send in
		   bugs, suggestions and improvements who keep me working on
		   the next version - yeah thanks a lot ;)

*/
/////////////////////////////////////////////////////////

// #pragma comment(lib,"Strmiids.lib") 

// #include <stdlib.h>
// #include <stdio.h>
// #include <math.h>
// #include <string.h>
// #include <wchar.h>
// #include <string>
// #include <vector>

//this is for TryEnterCriticalSection
// #ifndef _WIN32_WINNT
// 	#   define _WIN32_WINNT 0x501
// #endif
// #include <windows.h>


//Example Usage
/*
	//create a videoInput object
	videoInput VI;

	//Prints out a list of available devices and returns num of devices found
	int numDevices = VI.listDevices();

	int device1 = 0;  //this could be any deviceID that shows up in listDevices
	int device2 = 1;  //this could be any deviceID that shows up in listDevices

	//if you want to capture at a different frame rate (default is 30)
	//specify it here, you are not guaranteed to get this fps though.
	//VI.setIdealFramerate(dev, 60);

	//setup the first device - there are a number of options:

	VI.setupDevice(device1); 						  //setup the first device with the default settings
	//VI.setupDevice(device1, VI_COMPOSITE); 			  //or setup device with specific connection type
	//VI.setupDevice(device1, 320, 240);				  //or setup device with specified video size
	//VI.setupDevice(device1, 320, 240, VI_COMPOSITE);  //or setup device with video size and connection type

	//VI.setFormat(device1, VI_NTSC_M);					//if your card doesn't remember what format it should be
														//call this with the appropriate format listed above
														//NOTE: must be called after setupDevice!

	//optionally setup a second (or third, fourth ...) device - same options as above
	VI.setupDevice(device2);

	//As requested width and height can not always be accomodated
	//make sure to check the size once the device is setup

	int width 	= VI.getWidth(device1);
	int height 	= VI.getHeight(device1);
	int size	= VI.getSize(device1);

	unsigned char * yourBuffer1 = new unsigned char[size];
	unsigned char * yourBuffer2 = new unsigned char[size];

	//to get the data from the device first check if the data is new
	if(VI.isFrameNew(device1)){
		VI.getPixels(device1, yourBuffer1, false, false);	//fills pixels as a BGR (for openCV) unsigned char array - no flipping
		VI.getPixels(device1, yourBuffer2, true, true); 	//fills pixels as a RGB (for openGL) unsigned char array - flipping!
	}

	//same applies to device2 etc

	//to get a settings dialog for the device
	VI.showSettingsWindow(device1);


	//Shut down devices properly
	VI.stopDevice(device1);
	VI.stopDevice(device2);
*/


//////////////////////////////////////   VARS AND DEFS   //////////////////////////////////


//STUFF YOU DON'T CHANGE

//videoInput defines
public static final double VI_VERSION =	 0.200;
public static final int VI_MAX_CAMERAS =  20;
public static final int VI_NUM_TYPES =    19; //DON'T TOUCH
public static final int VI_NUM_FORMATS =  18; //DON'T TOUCH

//defines for setPhyCon - tuner is not as well supported as composite and s-video
public static final int VI_COMPOSITE = 0;
public static final int VI_S_VIDEO =   1;
public static final int VI_TUNER =     2;
public static final int VI_USB =       3;
public static final int VI_1394 =		 4;

//defines for formats
public static final int VI_NTSC_M =	0;
public static final int VI_PAL_B =	1;
public static final int VI_PAL_D =	2;
public static final int VI_PAL_G =	3;
public static final int VI_PAL_H =	4;
public static final int VI_PAL_I =	5;
public static final int VI_PAL_M =	6;
public static final int VI_PAL_N =	7;
public static final int VI_PAL_NC =	8;
public static final int VI_SECAM_B =	9;
public static final int VI_SECAM_D =	10;
public static final int VI_SECAM_G =	11;
public static final int VI_SECAM_H =	12;
public static final int VI_SECAM_K =	13;
public static final int VI_SECAM_K1 =	14;
public static final int VI_SECAM_L =	15;
public static final int VI_NTSC_M_J =	16;
public static final int VI_NTSC_433 =	17;

// added by gameover
public static final int VI_MEDIASUBTYPE_RGB24 =   0;
public static final int VI_MEDIASUBTYPE_RGB32 =   1;
public static final int VI_MEDIASUBTYPE_RGB555 =  2;
public static final int VI_MEDIASUBTYPE_RGB565 =  3;
public static final int VI_MEDIASUBTYPE_YUY2 =    4;
public static final int VI_MEDIASUBTYPE_YVYU =    5;
public static final int VI_MEDIASUBTYPE_YUYV =    6;
public static final int VI_MEDIASUBTYPE_IYUV =    7;
public static final int VI_MEDIASUBTYPE_UYVY =    8;
public static final int VI_MEDIASUBTYPE_YV12 =    9;
public static final int VI_MEDIASUBTYPE_YVU9 =    10;
public static final int VI_MEDIASUBTYPE_Y411 =    11;
public static final int VI_MEDIASUBTYPE_Y41P =    12;
public static final int VI_MEDIASUBTYPE_Y211 =    13;
public static final int VI_MEDIASUBTYPE_AYUV =    14;
public static final int VI_MEDIASUBTYPE_Y800 =    15;
public static final int VI_MEDIASUBTYPE_Y8 =      16;
public static final int VI_MEDIASUBTYPE_GREY =    17;
public static final int VI_MEDIASUBTYPE_MJPG =    18;
// Targeting ..\ICaptureGraphBuilder2.java


// Targeting ..\IGraphBuilder.java


// Targeting ..\IBaseFilter.java


// Targeting ..\IAMCrossbar.java


// Targeting ..\IMediaControl.java


// Targeting ..\ISampleGrabber.java


// Targeting ..\IMediaEventEx.java


// Targeting ..\IAMStreamConfig.java


// Targeting ..\_AMMediaType.java


// Targeting ..\SampleGrabberCallback.java



//keeps track of how many instances of VI are being used
//don't touch
public static native int comInitCount(); public static native void comInitCount(int setter);
// Targeting ..\videoDevice.java


// Targeting ..\videoInput.java



//  #endif


}
