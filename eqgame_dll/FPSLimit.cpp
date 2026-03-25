#include <Windows.h>
#include <stdio.h>
#include "common.h"

#pragma warning( disable : 4996)  // Disable warnings about not using _s version of functions.

static HWND* EQhWnd = reinterpret_cast<HWND*>(0x00807e04);
DWORD gFG_MAX=60;
DWORD SleepFG = 16;
DWORD SleepBG = 32;
DWORD CurMax = 0;
#define FRAME_COUNT 32
DWORD FrameArray[FRAME_COUNT + 1] = { 0 };
int CurrentFrame = 0;
int last_frame = 0;
BOOL bFrameArrayFilled = 0;
float FPS = 0.0f;

DWORD TimeNow = 0;
DWORD LastTime = 0;
DWORD FrameTime=0;
DWORD LastSleep=0;
bool frame_limiter = false;
bool was_background = true;

#define FPS_ABSOLUTE  0
#define FPS_CALCULATE 1

DWORD MaxFPSMode=FPS_CALCULATE;

void LoadIniSettings()
{
	char szResult[255];
	char szDefault[255];
	sprintf(szDefault, "%d",0);
	DWORD error = GetPrivateProfileStringA("Options",  "MaxFPS", szDefault, szResult, 255, "./eqclient.ini");
	if (GetLastError())
	{
		WritePrivateProfileStringA("Options", "MaxFPS", szDefault, "./eqclient.ini");
	}

	gFG_MAX = atoi(szResult);

	if (gFG_MAX > 0)
		SleepFG = (int)(1000.0f / (float)gFG_MAX);

	if (gFG_MAX <= 0)
		frame_limiter = false;

	char szResultChatKeepAlive[255];
	// turn on chat keepalive
	sprintf(szResultChatKeepAlive, "%d", 1);
	WritePrivateProfileStringA("Defaults", "ChatKeepAlive", szResultChatKeepAlive, "./eqclient.ini");

	char szResultFpsLimiter[255];
	char szDefaultFpsLimiter[255];
	sprintf(szDefaultFpsLimiter, "%d", 0);
	error = GetPrivateProfileStringA("Options", "UseFPSLimiter", szDefaultFpsLimiter, szResultFpsLimiter, 255, "./eqclient.ini");
	if (GetLastError())
	{
		WritePrivateProfileStringA("Options", "UseFPSLimiter", szDefaultFpsLimiter, "./eqclient.ini");
	}
	frame_limiter = (bool)(atoi(szResultFpsLimiter));
}

VOID ProcessFrame()
{
	// Update frame array
	DWORD Now = FrameArray[CurrentFrame] = GetTickCount();
	last_frame = CurrentFrame;
	DWORD FirstFrame = 0;
	DWORD Frames = CurrentFrame;
	if (bFrameArrayFilled)
	{
		FirstFrame = CurrentFrame + 1;
		if (FirstFrame>FRAME_COUNT)
		{
			FirstFrame = 0;
		}
		Frames = FRAME_COUNT;
	}
	// Calculate time this frame
	int LastFrame = CurrentFrame - 1;
	if (LastFrame<0)
	{
		if (bFrameArrayFilled)
		{
			LastFrame = FRAME_COUNT;
			FrameTime = Now - FrameArray[LastFrame];
		}
		else
		{
			FrameTime = 0;
		}
	}
	else
		FrameTime = Now - FrameArray[LastFrame];

	// Calculate FPS
	// Get amount of time between first frame and now
	DWORD Elapsed = Now - FrameArray[FirstFrame];

	if (Elapsed)
	{
		// less than one second?
		if (Elapsed<1000)
		{
			// elapsed 150 ms
			// extrapolate. how many frame arrays would fit in one second?
			FPS = (float)(1000.0f / (float)Elapsed);
			// 6.66667=1000/150
			// now multiply by the number of frames we've gone through
			// Frames 10
			FPS *= (float)Frames;
			// 66.6667= FPS * 10
			//		FPS=
		}
		else
		{
			// Frames = 100
			// Elapsed = 2000ms
			// FPS = 100 / (2000/1000) = 50

			// interpolate. how many seconds did it take for our frame array?
			FPS = (float)Frames / (float)((float)Elapsed / 1000.0f); // Frames / number of seconds
		}
	}
	else
		FPS = 999.0f;
	// advance frame count
	if (++CurrentFrame>FRAME_COUNT)
	{
		CurrentFrame = 0;
		bFrameArrayFilled = 1;
	}
}

bool mouse_looking = false;

void Pulse()
{
	*(DWORD*)0x008063D0 = 0;


	if (!frame_limiter)
		return;

	ProcessFrame();


	if (GetForegroundWindow() == *EQhWnd) {
		CurMax = gFG_MAX;
	}
	if (CurMax > 0) {
		int SleepTime = (int)(1000.0f / (float)CurMax);
		if (MaxFPSMode == FPS_CALCULATE) {
			// assume last frame time is constant, so a 30ms frame = 33 fps
			int SleepMax = SleepTime;
			SleepTime -= (FrameTime - LastSleep);
			if (SleepTime > SleepMax)
				SleepTime = SleepMax;
			if (SleepTime < 1) {
				SleepTime = 0;
				CurrentFrame = 1;
				FrameArray[0] = FrameArray[last_frame];
				bFrameArrayFilled = false;
			}
		}
		if (SleepTime > 0)
			Sleep(SleepTime);
		LastSleep = SleepTime;
	}



	/*if (GetForegroundWindow()==EQhWnd) {
		if (mouse_looking && gML_MAX > 0) {
			LastTime = TimeNow;
			TimeNow = GetTickCount();
			FrameTime = TimeNow - LastTime;
			FrameTime -= LastSleep;
			if (FrameTime >= 0 && FrameTime < SleepML) {
				int SleepTime = SleepML;
				SleepTime -= FrameTime;
				Sleep(SleepTime);
				LastSleep = SleepTime;
			}
			else {
				LastSleep = 0;
			}
		}
		else {
			if (gFG_MAX > 0) {
				LastTime = TimeNow;
				TimeNow = GetTickCount();
				FrameTime = TimeNow - LastTime;
				FrameTime -= LastSleep;
				if (FrameTime >= 0 && FrameTime < SleepFG) {
					int SleepTime = SleepFG;
					SleepTime -= FrameTime;
					Sleep(SleepTime);
					LastSleep = SleepTime;
				}
				else {
					LastSleep = 0;
				}
			}
		}
	} else {
		if (gBG_MAX > 0) {
			LastTime = TimeNow;
			TimeNow = GetTickCount();
			FrameTime = TimeNow - LastTime;
			FrameTime -= LastSleep;
			if (FrameTime >= 0 && FrameTime < SleepBG) {
				int SleepTime = SleepBG;
				SleepTime -= FrameTime;
				Sleep(SleepTime);
				LastSleep = SleepTime;
			}
			else {
				LastSleep = 0;
			}
		}
	}*/
}
