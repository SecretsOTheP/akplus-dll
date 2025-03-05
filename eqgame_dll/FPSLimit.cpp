#include <Windows.h>
#include <stdio.h>
#include "common.h"

HWND EQhWnd = 0;
HMODULE heqwMod = 0;
DWORD heqwModoff = 0;
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
int __cdecl InitKeys(int a1);
FUNCTION_AT_ADDRESS(int __cdecl InitKeys(int a1),0x55B7BC);
signed int FlushMouse();
FUNCTION_AT_ADDRESS(signed int FlushMouse(),0x55B5B9);

PMOUSECLICK EQADDR_MOUSECLICK=(PMOUSECLICK)0x798614;

BOOL gMouseLeftClickInProgress = FALSE;
BOOL gMouseRightClickInProgress = FALSE;

POINT savedRMousePos = POINT();

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

void SetEQhWnd()
{
	EQhWnd=*(HWND*)EQADDR_HWND;
	//lets check if they are using eqw if so, we need that window instad... -eqmule
	if (heqwMod) {
		//MessageBox(NULL, "Set EQ HWND", NULL, MB_OK);
		//DWORD GetEQWHWND=(DWORD)heqwMod+0x12C0; // eqw-2.35a
		DWORD GetEQWHWND=(DWORD)heqwMod+0x1670; // 0x1670 eqw-2.32 beta
		__asm {
			push eax;
			call [GetEQWHWND];
			mov [EQhWnd], eax;
			pop eax;
		};
	}
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

	if (*(DWORD *)0x007985EA == 0x00010001) {
		mouse_looking = true;
	}
	else
	{
		mouse_looking = false;
	}

	SetEQhWnd();


	if (!frame_limiter)
		return;

	ProcessFrame();


	if (GetForegroundWindow() == EQhWnd) {
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
