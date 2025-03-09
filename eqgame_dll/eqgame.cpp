#include <Windows.h>
#include <stdio.h>
#include <map>
#include <time.h>
#include "..\Detours\inc\detours.h"
//#include "..\zlib_x86\include\zlib.h"
#include "eqmac.h"
#include "eqmac_functions.h"
#include "eqgame.h"
#include <dxgi.h>
#include <ctime>
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <iomanip>
#include <random>
#include <functional>
#include <vector>

// Sent on zone entry to the server.
// Server uses this to tell the user if they are out of date.
// Increment if we make significant changes that we want to track.
// Server uses Quarm:WarnDllVersionBelow to warn clients below a specific threshold.
#ifndef DLL_VERSION
#define DLL_VERSION 1
#endif
#define DLL_VERSION_MESSAGE_ID 4 // Matches ClientFeature::CodeVersion == 4 on the Server, do not change.

#define BYTEn(x, n) (*((BYTE*)&(x)+n))
#define BYTE1(x) BYTEn(x, 0)
#define BYTE2(x) BYTEn(x, 1)
//#include "Common.h"

#define FREE_THE_MOUSE
//#define GM_MODE
//#define LOGGING
//#define HORSE_LOGGING 1
extern void Pulse();
extern bool was_background;
extern void LoadIniSettings();
extern void SetEQhWnd();
extern HMODULE heqwMod;
extern HWND EQhWnd;
HANDLE myproc = 0;
bool title_set = false;
std::string new_title("");
bool first_maximize = true;
bool can_fullscreen = false;
bool ignore_right_click = false;
bool ignore_right_click_up = false;
bool ignore_left_click = false;
bool ignore_left_click_up = false;
DWORD focus_regained_time = 0;

bool ResolutionStored = false;
DWORD resx = 0;
DWORD resy = 0;
DWORD bpp = 0;
DWORD refresh = 0;
HMODULE eqmain_dll = 0;
BOOL bExeChecksumrequested = 0;
BOOL g_mouseWheelZoomIsEnabled = true;
unsigned int g_buffWindowTimersFontSize = 3;
bool has_focus = true;
WINDOWINFO stored_window_info;
bool window_info_stored = false;
WINDOWPLACEMENT g_wpPrev = { sizeof(g_wpPrev) };
bool start_fullscreen = false;
bool startup = true;
POINT posPoint;
DWORD o_MouseEvents = 0x0055B3B9;
DWORD o_MouseCenter = 0x0055B722;

bool g_bEnableBrownSkeletons = false;
bool g_bEnableExtendedNameplates = true;
bool g_bSongWindowAutoHide = false;
bool auto_login = false;
char UserName[64];
char PassWord[64];

// [BuffStackingPatch] Values are modified via the OnZone handshake
bool Rule_Buffstacking_Patch_Enabled = false;
int Rule_Num_Short_Buffs = 0;
int Rule_Max_Buffs = EQ_NUM_BUFFS;

typedef signed int(__cdecl* ProcessGameEvents_t)();
ProcessGameEvents_t return_ProcessGameEvents;
ProcessGameEvents_t return_ProcessMouseEvent;
//ProcessGameEvents_t return_SetMouseCenter;

DWORD d3ddev = 0;
DWORD eqgfxMod = 0;
BOOL bWindowedMode = true;

BOOL RightHandMouse = true;

// Callbacks run on zone
std::vector<std::function<void()>> OnZoneCallbacks;
std::vector<std::function<void(CDisplay*)>> InitGameUICallbacks;
std::vector<std::function<void()>> DeactivateUICallbacks;
std::vector<std::function<void(char)>> ActivateUICallbacks;
std::vector<std::function<void()>> CleanUpUICallbacks;

// Callbacks run on custom messages received via OP_SpawnAppearance
std::vector<std::function<bool(DWORD feature_id,DWORD feature_value, bool is_request)>> CustomSpawnAppearanceMessageHandlers;

typedef struct _detourinfo
{
	DWORD_PTR tramp;
	DWORD_PTR detour;
}detourinfo;
std::map<DWORD,_detourinfo> ourdetours;


#define FUNCTION_AT_ADDRESS(function,offset) __declspec(naked) function\
{\
	__asm{mov eax, offset};\
	__asm{jmp eax};\
}

#define EzDetour(offset,detour,trampoline) AddDetourf((DWORD)offset,detour,trampoline)

void PatchA(LPVOID address, const void *dwValue, SIZE_T dwBytes) {
	unsigned long oldProtect;
	VirtualProtect((void *)address, dwBytes, PAGE_EXECUTE_READWRITE, &oldProtect);
	memcpy((void *)address, dwValue, dwBytes);
	FlushInstructionCache(GetCurrentProcess(), (void*)address, dwBytes);
	VirtualProtect((void *)address, dwBytes, oldProtect, &oldProtect);
}

// copies target original value to buffer, then copies source to the target
void PatchSwap(int target, BYTE* source, SIZE_T size, BYTE* buffer = nullptr)
{
	DWORD oldprotect;
	VirtualProtect((PVOID*)target, size, PAGE_EXECUTE_READWRITE, &oldprotect);
	if (buffer)
		memcpy((void*)buffer, (const void*)target, size);
	memcpy((void*)target, (const void*)source, size);
	FlushInstructionCache(GetCurrentProcess(), (void*)target, size);
	VirtualProtect((PVOID*)target, size, oldprotect, &oldprotect);
}

// Patch 'call <Function>' instruction with a new function address
void PatchCall(uintptr_t call_address, uintptr_t new_func_addr)
{
	unsigned long oldProtect;
	uintptr_t relativeOffset = new_func_addr - (call_address + 5);
	VirtualProtect((void*)call_address, 5, PAGE_EXECUTE_READWRITE, &oldProtect);
	*(BYTE*)call_address = 0xE8;  // call opcode
	*(uintptr_t*)(call_address + 1) = relativeOffset;  // new offset
	FlushInstructionCache(GetCurrentProcess(), (void*)call_address, 5);
	VirtualProtect((void*)call_address, 5, oldProtect, &oldProtect);
}

// start_address (Inclusive), until_address (Exclusive)
void PatchNopByRange(int start_address, int until_address) {

	int size = until_address - start_address;
	if (size <= 0) {
		return;
	}

	int target = start_address;
	BYTE nop2[] = { 0x66, 0x90 }; // 0x66 0x99 (safe, officially recognized as a 2-byte NOP).

	DWORD oldprotect;
	VirtualProtect((PVOID*)start_address, size, PAGE_EXECUTE_READWRITE, &oldprotect);

	while (size >= 2) {
		memcpy((void*)target, nop2, 2);
		size -= 2;
		target += 2;
	}
	if (size == 1) {
		memcpy((void*)target, &nop2[1], 1);
	}

	FlushInstructionCache(GetCurrentProcess(), (void*)start_address, size);
	VirtualProtect((PVOID*)start_address, size, oldprotect, &oldprotect);
}

void UpdateTitle()
{
	if (new_title.length() == 0) {
		HWND cur = NULL;
		char str[255];
		int i = 0;
		do {
			i++;
			sprintf(str, "Client%d", i);
			cur = FindWindowA(NULL, str);
		} while (cur != NULL);
		new_title = str;
	}
	SetWindowTextA(EQhWnd, new_title.c_str());
#ifdef LOGGING
	std::string outlog_name(new_title);
	outlog_name += ".log";
	freopen(outlog_name.c_str(), "w", stdout);
#endif // LOGGING
}
#ifdef LOGGING
void WriteLog(std::string logstring) {

	std::time_t result = std::time(nullptr);
	std::tm * ptm = std::localtime(&result);
	if (new_title.length() > 0)
		std::cout << "[" << new_title.c_str() << "] [" << std::put_time(ptm, "%c") << "] " << logstring.c_str() << std::endl;
	else
		std::cout << "[" << std::put_time(ptm, "%c") << "] " << logstring.c_str() << std::endl;
	OutputDebugString(logstring.c_str());
	//MessageBox(NULL, outstring.c_str(), NULL, MB_OK);
}
#endif // !LOGGING

typedef void(__thiscall* PrintChat)(int this_ptr, const char* data, short color, bool un);
void print_chat(const char* format, ...)
{
	static PrintChat print_chat_internal = (PrintChat)0x537f99;
	va_list argptr;
	char buffer[512];
	va_start(argptr, format);
	vsnprintf(buffer, 511, format, argptr);
	va_end(argptr);
	print_chat_internal(*(int*)0x809478, buffer, 0, true);
}

void __cdecl ResetMouseFlags() {
#ifdef LOGGING
	WriteLog("EQGAME: Resetting Mouse Flags");
#endif
	DWORD ptr = *(DWORD *)0x00809DB4;
	if (ptr)
	{
		*(BYTE*)(ptr + 85) = 0;
		*(BYTE*)(ptr + 86) = 0;
		*(BYTE*)(ptr + 87) = 0;
		*(BYTE*)(ptr + 88) = 0;
	}

	*(DWORD*)0x00809320 = 0;
	*(DWORD*)0x0080931C = 0;
	*(DWORD*)0x00809324 = 0;
	*(DWORD*)0x00809328 = 0;
	*(DWORD*)0x0080932C = 0;
}

void __cdecl ProcessAltState() {
	if(GetForegroundWindow() == EQhWnd)
	{
		if(GetAsyncKeyState(VK_MENU)&0x8000) // alt key is pressed
		{
			DWORD ptr = *(DWORD *)0x00809DB4;
			if (ptr)
			{
				*(BYTE*)(ptr + 87) = 1;
			}
			*(DWORD*)0x00799740 = 1;
			*(DWORD*)0x0080932C = 1;
		}
		else
		{
			DWORD ptr = *(DWORD *)0x00809DB4;
			if (ptr)
			{
				*(BYTE*)(ptr + 87) = 0;
			}
			*(DWORD*)0x00799740 = 0;
			*(DWORD*)0x0080932C = 0;
		}
		if (GetAsyncKeyState(VK_CONTROL) & 0x8000) // ctrl key is pressed
		{
			DWORD ptr = *(DWORD *)0x00809DB4;
			if (ptr)
			{
				*(BYTE*)(ptr + 86) = 1;
			}
			*(DWORD*)0x0079973C = 1;
			*(DWORD*)0x00809320 = 1;
		}
		else
		{
			DWORD ptr = *(DWORD *)0x00809DB4;
			if (ptr)
			{
				*(BYTE*)(ptr + 86) = 0;
			}
			*(DWORD*)0x0079973C = 0;
			*(DWORD*)0x00809320 = 0;
		}
		if (GetAsyncKeyState(VK_SHIFT) & 0x8000) // shift key is pressed
		{
			DWORD ptr = *(DWORD *)0x00809DB4;
			if (ptr)
			{
				*(BYTE*)(ptr + 85) = 1;
			}
			*(DWORD*)0x00799738 = 1;
			*(DWORD*)0x0080931C = 1;
		}
		else
		{
			DWORD ptr = *(DWORD *)0x00809DB4;
			if (ptr)
			{
				*(BYTE*)(ptr + 85) = 0;
			}
			*(DWORD*)0x00799738 = 0;
			*(DWORD*)0x0080931C = 0;
		}
	}
}

void AddDetourf(DWORD address, ...)
{
	va_list marker;
	int i=0;
	va_start(marker, address);
	DWORD Parameters[3];
	DWORD nParameters=0;
	while (i!=-1) 
	{
		if (nParameters<3)
		{
			Parameters[nParameters]=i;
			nParameters++;
		}
		i = va_arg(marker,int);
	}
	va_end(marker);
	if (nParameters==3)
	{
		detourinfo detinf = {0};
		detinf.detour = Parameters[1];
		detinf.tramp = Parameters[2];
		ourdetours[address] = detinf;
		DetourFunctionWithEmptyTrampoline((PBYTE)detinf.tramp,(PBYTE)address,(PBYTE)detinf.detour);
	}
}

bool CtrlPressed() {
	return *(DWORD*)0x00809320 > 0;
}
bool AltPressed() {
	return *(DWORD*)0x0080932C > 0;
}
bool ShiftPressed() {
	return *(DWORD*)0x0080931C > 0;
}

// Helper - Executes all callbacks in 'OnZoneCallbacks'
typedef void(__thiscall* EQ_FUNCTION_TYPE_EnterZone)(void* this_ptr, int hwnd);
EQ_FUNCTION_TYPE_EnterZone EnterZone_Trampoline;
void __fastcall EnterZone_Detour(void* this_ptr, int unused, int hwnd) {
	EnterZone_Trampoline(this_ptr, hwnd);
	for (auto& callback : OnZoneCallbacks) {
		callback();
	}
}

// Helper - Executes all callbacks in 'InitGameUICallbacks'
typedef int(__thiscall* EQ_FUNCTION_TYPE_InitGameUI)(CDisplay* cdisplay);
EQ_FUNCTION_TYPE_InitGameUI InitGameUI_Trampoline;
int __fastcall InitGameUI_Detour(CDisplay* cdisplay, int unused)
{
	int res = InitGameUI_Trampoline(cdisplay);
	for (auto& callback : InitGameUICallbacks) {
		callback(cdisplay);
	}
	return res;
}

// Helper - Executes all callbacks in 'CleanUpUICallbacks'
typedef void*(* EQ_FUNCTION_TYPE_CleanUpUI)(void);
EQ_FUNCTION_TYPE_CleanUpUI CleanUpUI_Trampoline;
void* CleanUpUI_Detour()
{
	void* res = CleanUpUI_Trampoline();
	for (auto& callback : CleanUpUICallbacks) {
		callback();
	}
	return res;
}

// Helper - Executes all callbacks in 'ActivateUICallbacks'
typedef int(__stdcall* EQ_FUNCTION_TYPE_ActivateUI)(char a1);
EQ_FUNCTION_TYPE_ActivateUI ActivateUI_Trampoline;
int __stdcall ActivateUI_Detour(char a1)
{
	int res = ActivateUI_Trampoline(a1);
	for (auto& callback : ActivateUICallbacks) {
		callback(a1);
	}
	return res;
}

// Helper - Executes all callbacks in 'DeactivateUICallbacks'
typedef int(* EQ_FUNCTION_TYPE_DeactivateUI)(void);
EQ_FUNCTION_TYPE_DeactivateUI DeactivateUI_Trampoline;
int DeactivateUI_Detour() {
	int res = DeactivateUI_Trampoline();
	for (auto& callback : DeactivateUICallbacks) {
		callback();
	}
	return res;
}

// Helper - Sends custom key/value data to the server using OP_SpawnAppearance (type = 256)
void SendCustomSpawnAppearanceMessage(unsigned __int16 feature_id, unsigned __int16 feature_value, bool is_request) {

	DWORD id = feature_id;
	DWORD value = feature_value;

	SpawnAppearance_Struct message;
	message.type = SpawnAppearanceType_ClientDllMessage; // AppearanceType::ClientDllMessage on server
	message.spawn_id = 0;
	message.parameter = (id << 16) | value;
	if (is_request)
		message.parameter &= 0x7FFFFFFFu;
	else
		message.parameter |= 0x80000000u;
	reinterpret_cast<void(__cdecl*)(int* connection, DWORD opcode, void* buffer, DWORD size, int unknown)>(EQ_FUNCTION_send_message)((int*)0x7952fc, 16629, &message, sizeof(SpawnAppearance_Struct), 0); // Connection::SendMessage(..)
}

// Helper - Executes all callback handlers for custom SpawnAppearanceMessages
void HandleCustomSpawnAppearanceMessage(SpawnAppearance_Struct* message)
{
	// TODO: Maybe in the future we could encode data into spawn_id field too, but let's keep it simple for now.
	if (message->type == SpawnAppearanceType_ClientDllMessage && message->spawn_id == 0) {
		bool is_request = (message->parameter >> 31) == 0;
		DWORD feature_id = message->parameter >> 16 & 0x7FFFu;
		DWORD feature_value = message->parameter & 0xFFFFu;
		for (auto& handler : CustomSpawnAppearanceMessageHandlers) {
			if (handler(feature_id, feature_value, is_request)) {
				return;
			}
		}
	}
}
// Hook to delegate to HandleCustomSpawnAppearanceMessage
typedef int(__thiscall* EQ_FUNCTION_TYPE_HandleSpawnAppearanceMessage)(void* this_ptr, int unk2, int opcode, SpawnAppearance_Struct* sa);
EQ_FUNCTION_TYPE_HandleSpawnAppearanceMessage HandleSpawnAppearanceMessage_Trampoline;
int __fastcall HandleSpawnAppearanceMessage_Detour(void* this_ptr, int unused_edx, int unk2, int opcode, SpawnAppearance_Struct* sa) {
	if (sa->type >= SpawnAppearanceType_ClientDllMessage) {
		HandleCustomSpawnAppearanceMessage(sa);
		return 1;
	}
	return HandleSpawnAppearanceMessage_Trampoline(this_ptr, unk2, opcode, sa);
}

typedef bool(__cdecl* EQ_FUNCTION_TYPE_GetLabelFromEQ)(int, PEQCXSTR*, bool*, DWORD*);
EQ_FUNCTION_TYPE_GetLabelFromEQ GetLabelFromEQ_Trampoline;
bool __cdecl GetLabelFromEQ_Detour(int EqType, PEQCXSTR* str, bool* override_color, DWORD* color)
{
	switch (EqType) {
	case 135: // Song1
	case 136: // Song2
	case 137: // Song3
	case 138: // Song4
	case 139: // Song5
	case 140: // Song6
	case 141: // Song7
	case 142: // Song8
	case 143: // Song9
	case 144: // Song10
	case 145: // Song11
	case 146: // Song12
	case 147: // Song13
	case 148: // Song14
	case 149: // Song15
		*override_color = false;
		if (EQ_OBJECT_CharInfo) {
			EQBUFFINFO& buff = EQ_OBJECT_CharInfo->BuffsExt[EqType - 135];
			if (EQ_Spell::IsValidSpellIndex(buff.SpellId)) {
				EQSPELLINFO* spell = EQ_Spell::GetSpell(buff.SpellId);
				if (spell) {
					EQ_CXStr_Set(str, spell->Name);
					return true;
				}
			}
		}
		EQ_CXStr_Set(str, "");
		return true;
	}
	return GetLabelFromEQ_Trampoline(EqType, str, override_color, color);
}

bool g_bEnableClassicMusic = false;

int g_LastMusicStop = 0;
int g_curMusicTrack = 2;
int g_curGlobalMusicTrack = 0;
bool bIsWaterPlaying = false;
int g_prevGlobalMusicTrack = 0;

int __cdecl msg_send_corpse_equip(class EQ_Equipment *);
FUNCTION_AT_ADDRESS(int __cdecl msg_send_corpse_equip(class EQ_Equipment *),0x4DF03D);
int base_val = 362;
class Eqmachooks {
public:

	int  CEQMusicManager__Set_Trampoline(int, int, int, int, int, int, int, int, int);
	int  CEQMusicManager__Set_Detour(int musicIdx, int unknown1, int trackIdx, int volume, int unknown, int timeoutDelay, int timeInDelay, int range /* ? */, int bIsMp3)
	{
		if (musicIdx == 2 && g_bEnableClassicMusic)
		{
			CEQMusicManager__Set_Trampoline(2500, unknown1, 0, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2501, unknown1, 1, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2502, unknown1, 2, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2503, unknown1, 3, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2504, unknown1, 4, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2505, unknown1, 5, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2506, unknown1, 6, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2507, unknown1, 7, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2508, unknown1, 8, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2509, unknown1, 9, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2510, unknown1, 10, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2511, unknown1, 11, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2512, unknown1, 12, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2513, unknown1, 13, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2514, unknown1, 14, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2515, unknown1, 15, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2516, unknown1, 16, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2517, unknown1, 17, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2518, unknown1, 18, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2519, unknown1, 19, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2520, unknown1, 20, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2521, unknown1, 21, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
			CEQMusicManager__Set_Trampoline(2522, unknown1, 22, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);
		}

		return CEQMusicManager__Set_Trampoline(musicIdx, unknown1, trackIdx, volume, unknown, timeoutDelay, timeInDelay, range, bIsMp3);

	}

	int  CEQMusicManager__Play_Trampoline(int, int);
	int  CEQMusicManager__Play_Detour(int trackIdx, int bStartStop)
	{
		if (g_bEnableClassicMusic)
		{

			std::random_device rd;
			std::mt19937 mt(rd());
			std::uniform_int_distribution<int> dist(1, 3);
			auto tickCount = GetTickCount();

			if (trackIdx == 2)
			{
				if (g_LastMusicStop == 0)
				{
					g_LastMusicStop = tickCount;
				}

				if (bStartStop == 1)
				{
					if (tickCount >= g_LastMusicStop + 10000)
					{
						switch (dist(mt))
						{
						case 1:
						{
							g_curMusicTrack = 2501;
							break;
						}
						case 2:
						{
							g_curMusicTrack = 2502;
							break;
						}
						case 3:
						default:
						{
							g_curMusicTrack = 2500;
							break;
						}
						}
					}
					trackIdx = g_curMusicTrack;
				}
				else if (bStartStop == 0)
				{
					trackIdx = g_curMusicTrack;
					g_LastMusicStop = GetTickCount();
				}
			}
		}
		if (bStartStop == 1)
		{
			g_curGlobalMusicTrack = trackIdx;
		}
		else
		{
			g_curGlobalMusicTrack = 0;
		}

		return CEQMusicManager__Play_Trampoline(trackIdx, bStartStop);

	}

	int  CEQMusicManager__WavPlay_Trampoline(int, int);
	int  CEQMusicManager__WavPlay_Detour(int wavIdx, int soundControl)
	{
		if (g_bEnableClassicMusic)
		{
			if (wavIdx == 100 && !bIsWaterPlaying)
			{
				if (g_curGlobalMusicTrack != 0 && g_curGlobalMusicTrack != 2509)
				{
					g_prevGlobalMusicTrack = g_curGlobalMusicTrack;
					CEQMusicManager__Play_Trampoline(g_curGlobalMusicTrack, 0);
				}
				CEQMusicManager__Play_Trampoline(2508, 1);
				bIsWaterPlaying = true;
			}
			else if(wavIdx == 99 && bIsWaterPlaying)
			{
				int prevTrack = g_prevGlobalMusicTrack;
				CEQMusicManager__Play_Trampoline(2508, 0);
				if (g_prevGlobalMusicTrack != 0)
					CEQMusicManager__Play_Trampoline(g_prevGlobalMusicTrack, 1);
				bIsWaterPlaying = false;
			}
		}

		return CEQMusicManager__WavPlay_Trampoline(wavIdx, soundControl);
	}

	unsigned char CEverQuest__HandleWorldMessage_Trampoline(DWORD *,unsigned __int32,char *,unsigned __int32);
	unsigned char CEverQuest__HandleWorldMessage_Detour(DWORD *con,unsigned __int32 Opcode,char *Buffer,unsigned __int32 len)
	{
		//std::cout << "Opcode: 0x" << std::hex << Opcode << std::endl;
		if(Opcode==0x4052) {//OP_ItemOnCorpse
			return msg_send_corpse_equip((EQ_Equipment*)Buffer);
		}
		else if (Opcode == 0x4038) { // OP_ShopDelItem=0x3840
			if (!*(BYTE*)0x8092D8) {
				return NULL;
				// stone skin UI doesn't like this
				/*
				Merchant_DelItem_Struct* mds = (Merchant_DelItem_Struct*)(Buffer + 2);
				std::string outstring;
				outstring = "MDS npcid = ";
				outstring += std::to_string(mds->npcid);
				outstring += " slot = ";
				outstring += std::to_string(mds->itemslot);
				WriteLog(outstring);
				if (!mds->itemslot || mds->itemslot > 29)
					return NULL;
				*/
			}
				
		}
		/*if (Opcode == 0x400C) {
			// not using new UI
			if (!*(BYTE*)0x8092D8) {

				if (len > 2) {
					unsigned char *buff = new unsigned char[28960];
					memcpy(buff, Buffer, 2);
					int newsize = InflatePacket((unsigned char*)(Buffer + 2), len - 2, buff, 28960);
					std::string outstring;
					outstring = "Merchant inventory uncompressed size = ";
					outstring += " newsize = ";
					outstring += std::to_string(newsize);
					WriteLog(outstring);
					if (newsize > 0) {
						unsigned char* newbuff = new unsigned char[28960];
						memcpy(newbuff, buff, base_val);
						unsigned char* outbuff = new unsigned char[28960];
						int outsize = DeflatePacket((const unsigned char*)newbuff, base_val, outbuff, 28960);
						if (outsize > 0) {
							outstring = "Merchant inventory uncompressed size = ";
							outstring += "outsize = ";
							outstring += std::to_string(outsize);
							WriteLog(outstring);
							memcpy((unsigned char*)(buff + 2), outbuff, outsize);
							base_val += 362;
							return CEverQuest__HandleWorldMessage_Trampoline(con, Opcode, (char *)buff, outsize + 2);
						}
					}
					outstring = "Merchant inventory uncompressed size = ";
					outstring += std::to_string(newsize);
					outstring += " input sizeof Buffer = ";
					outstring += std::to_string(sizeof(Buffer));
					outstring += " input len = ";
					outstring += std::to_string(len);
					WriteLog(outstring);
					
				}
			}
		}*/
		else if (Opcode == 0x41d8) { // OP_LogServer=0xc341
			can_fullscreen = true;
#ifdef LOGGING
			WriteLog("EQGAME: CEverQuest__HandleWorldMessage_Detour OP_LogServer=0xc341 Can go Fullscreen (1)");
#endif
		}
		else if (Opcode == 0x4092 && len >= sizeof(WearChange_Struct))
		{
			Handle_In_OP_WearChange((WearChange_Struct*)Buffer);
		}
		return CEverQuest__HandleWorldMessage_Trampoline(con,Opcode,Buffer,len);
	}

	int __cdecl  CDisplay__Process_Events_Trampoline();
	int __cdecl  CDisplay__Process_Events_Detour(){
		if (EQ_OBJECT_CEverQuest != NULL && EQ_OBJECT_CEverQuest->GameState > 0 && EQ_OBJECT_CEverQuest->GameState != 255 && can_fullscreen) {
			SetEQhWnd();
			ProcessAltState();
			if (!ResolutionStored && *(DWORD*)(0x007F97D0) != 0)
			{
				DWORD ptr = *(DWORD*)(0x007F97D0);

				resx = *(DWORD*)(ptr + 0x7A28);
				resy = *(DWORD*)(ptr + 0x7A2C);
				bpp = *(DWORD*)(ptr + 0x7A20);
				refresh = *(DWORD*)(ptr + 0x7A30);

				ResolutionStored = true;
				eqgfxMod = *(DWORD*)(0x007F9C50);
				d3ddev = (DWORD)(eqgfxMod + 0x00A4F92C);
#ifdef LOGGING
				std::string outstring;
				outstring = "EQGAME: Resolution Stored: resx = ";
				outstring += std::to_string(resx);
				outstring += " resy = ";
				outstring += std::to_string(resy);
				outstring += " bbp = ";
				outstring += std::to_string(bpp);
				outstring += " refresh = ";
				outstring += std::to_string(refresh);
				WriteLog(outstring);
#endif
			}
			
			if (ResolutionStored && startup && GetForegroundWindow() == EQhWnd && !IsIconic(EQhWnd)) {
#ifdef LOGGING
				WriteLog("EQGAME: Startup - Storing window info");
#endif
				GetWindowInfo(EQhWnd, &stored_window_info);
				window_info_stored = true;
				startup = false;
				/*
				MONITORINFO monitor_info;
				monitor_info.cbSize = sizeof(monitor_info);
				GetMonitorInfo(MonitorFromWindow(EQhWnd, MONITOR_DEFAULTTONEAREST),
					&monitor_info);
				RECT window_rect(monitor_info.rcMonitor);
				DWORD monitor_x = window_rect.right - window_rect.left;
				DWORD monitor_y = window_rect.bottom - window_rect.top;
				if (monitor_x != resx || monitor_y != resy) {
					// Monitor resolution does not match game resolution
					// block initial going full screen in auto mode
					start_fullscreen = false;
					WriteLog("Startup - Monitor resolution does not match game - blocking auto full screen");
				}
#ifdef LOGGING
				std::string outstring;
				outstring = "Monitor Info: resx = ";
				outstring += std::to_string(monitor_x);
				outstring += " resy = ";
				outstring += std::to_string(monitor_y);
				WriteLog(outstring);
#endif

				*/

			}
			if (start_fullscreen && bWindowedMode && GetForegroundWindow() == EQhWnd && !IsIconic(EQhWnd)) {
				// This takes if fullscreen initially
#ifdef LOGGING
				WriteLog("EQGAME: Going Fullscreen (1)");
#endif
				if (!window_info_stored) {
#ifdef LOGGING
					WriteLog("EQGAME: Storing Window Info (1)");
#endif
					GetWindowInfo(EQhWnd, &stored_window_info);
					window_info_stored = true;
				}
				// MessageBox(NULL, "Going Full Screen", NULL, MB_OK);
				SetWindowLong(EQhWnd, GWL_STYLE,
					stored_window_info.dwStyle & ~(WS_CAPTION | WS_THICKFRAME | WS_SYSMENU));

				SetWindowLong(EQhWnd, GWL_EXSTYLE,
					stored_window_info.dwExStyle & ~(WS_EX_DLGMODALFRAME |
						WS_EX_WINDOWEDGE | WS_EX_CLIENTEDGE | WS_EX_STATICEDGE));

				MONITORINFO monitor_info;
				monitor_info.cbSize = sizeof(monitor_info);
				GetMonitorInfo(MonitorFromWindow(EQhWnd, MONITOR_DEFAULTTONEAREST),
					&monitor_info);
				RECT window_rect(monitor_info.rcMonitor);

				WINDOWPLACEMENT window_placement;
				window_placement.length = sizeof(window_placement);
				
				if (first_maximize) {
					GetWindowPlacement(EQhWnd, &window_placement);
					window_placement.showCmd = SW_MINIMIZE;
					SetWindowPlacement(EQhWnd, &window_placement);
					window_placement.showCmd = SW_MAXIMIZE;
					SetWindowPlacement(EQhWnd, &window_placement);
#ifdef LOGGING
					WriteLog("EQGAME: Going Fullscreen First Maximize (2)");
#endif
				}
				SetWindowPos(EQhWnd, HWND_TOP, window_rect.left, window_rect.top,
					window_rect.right - window_rect.left, window_rect.bottom - window_rect.top,
					SWP_NOOWNERZORDER | SWP_FRAMECHANGED | SWP_NOSENDCHANGING | SWP_SHOWWINDOW);

				bWindowedMode = false;	
				first_maximize = false;
			}
			if (GetForegroundWindow() == EQhWnd && !IsIconic(EQhWnd)) {
				if (!has_focus) {
#ifdef LOGGING
					WriteLog("EQGAME: Window Regained focus after lost focus.");
#endif
					focus_regained_time = GetTickCount();
					ResetMouseFlags();
					while (ShowCursor(FALSE) >= 0);
					// regained focus
					if (ResolutionStored) {
						if (heqwMod) {
							int result;
							result = (*(int(__stdcall **)(DWORD))(**(DWORD **)d3ddev + 12))(*(DWORD *)d3ddev);
							//char str[56];
							//sprintf(str, "TestCoop = %d", result);
							//MessageBox(NULL, str, NULL, MB_OK);
							if (result == -2005530519 || result == -2005530520) {
#ifdef LOGGING
								WriteLog("EQGAME: d3d device failed - reinitializing 3d device");
#endif
								*(DWORD*)0x005FE990 = resx;
								*(DWORD*)0x005FE994 = resy;
								*(DWORD*)0x005FE998 = bpp;
								*(DWORD*)0x0063AE8C = refresh;
								((int(__cdecl*)())0x0043BBE2)();
							}
						}
						else {
							// when in full screen mode, this will end up killing window.
								*(DWORD*)0x005FE990 = resx;
								*(DWORD*)0x005FE994 = resy;
								*(DWORD*)0x005FE998 = bpp;
								*(DWORD*)0x0063AE8C = refresh;
								((int(__cdecl*)())0x0043BBE2)();
						}
					}
				}
				if (!ResolutionStored && *(DWORD*)(0x007F97D0) != 0)
				{
#ifdef LOGGING
					WriteLog("EQGAME: Storing Resolution Info (2)");
#endif
					DWORD ptr = *(DWORD*)(0x007F97D0);

					resx = *(DWORD*)(ptr + 0x7A28);
					resy = *(DWORD*)(ptr + 0x7A2C);
					bpp = *(DWORD*)(ptr + 0x7A20);
					refresh = *(DWORD*)(ptr + 0x7A30);

					ResolutionStored = true;
					eqgfxMod = *(DWORD*)(0x007F9C50);
					d3ddev = (DWORD)(eqgfxMod + 0x00A4F92C);

				}
				has_focus = true;
			}
			else {
				if (has_focus) {
#ifdef LOGGING
					WriteLog("EQGAME: Lost focus of window.  Different process in foreground.");
#endif
					ResetMouseFlags();
					ignore_right_click = true;
					ignore_left_click = true;
					focus_regained_time = 0;
					while (ShowCursor(TRUE) < 0);
				}
				has_focus = false;
				return 0;
			}
		}
		else if (!bWindowedMode && EQ_OBJECT_CEverQuest == NULL) {
			SetEQhWnd();
			ProcessAltState();
			SetWindowLong(EQhWnd, GWL_STYLE, stored_window_info.dwStyle | WS_CAPTION );
			SetWindowLong(EQhWnd, GWL_EXSTYLE, stored_window_info.dwExStyle);
#ifdef LOGGING
			WriteLog("EQGAME: EQ Object found Null Dropping Fullscreen (1)");
#endif
			if (!IsIconic(EQhWnd) && window_info_stored) {
				SetWindowPos(EQhWnd, HWND_TOP, stored_window_info.rcWindow.left, stored_window_info.rcWindow.top,
					stored_window_info.rcWindow.right - stored_window_info.rcWindow.left, stored_window_info.rcWindow.bottom - stored_window_info.rcWindow.top,
					SWP_NOOWNERZORDER | SWP_FRAMECHANGED | SWP_NOSENDCHANGING | SWP_SHOWWINDOW);
			}
			can_fullscreen = false;
			bWindowedMode = true;
			start_fullscreen = true;
			first_maximize = true;
		}
		SetEQhWnd();
		if (EQhWnd == GetForegroundWindow())
		{
			return CDisplay__Process_Events_Trampoline();
		}
		return 0;
	}
	int CDisplay__Render_World_Trampoline();
	int CDisplay__Render_World_Detour()
	{
		Pulse();
		return CDisplay__Render_World_Trampoline();
	}

	// Level of Detail preference bug fix
	int CDisplay__StartWorldDisplay_Trampoline(int zoneindex, int x);
	int CDisplay__StartWorldDisplay_Detour(int zoneindex, int x)
	{
		// this function always sets LoD to on, regardless of the user's preference
		int ret = CDisplay__StartWorldDisplay_Trampoline(zoneindex, x);

		int lod = *(char *)0x798AE8; // this is the preference the user has selected, loaded from eqOptions1.opt
		float(__cdecl * s3dSetDynamicLOD)(DWORD, float, float) = *(float(__cdecl **)(DWORD, float, float))0x007F986C; // this is a variable holding the pointer to the gfx dll function
		s3dSetDynamicLOD(lod, 1.0f, 100.0f); // apply the user's setting for real

		return ret;
	}
};

DETOUR_TRAMPOLINE_EMPTY(unsigned char Eqmachooks::CEverQuest__HandleWorldMessage_Trampoline(DWORD *,unsigned __int32,char *,unsigned __int32));
DETOUR_TRAMPOLINE_EMPTY(int Eqmachooks::CEQMusicManager__Set_Trampoline(int, int, int, int, int, int, int, int, int));
DETOUR_TRAMPOLINE_EMPTY(int Eqmachooks::CEQMusicManager__Play_Trampoline(int, int));
DETOUR_TRAMPOLINE_EMPTY(int Eqmachooks::CEQMusicManager__WavPlay_Trampoline(int, int));
DETOUR_TRAMPOLINE_EMPTY(int __cdecl CEverQuest__DisplayScreen_Trampoline(char *));
DETOUR_TRAMPOLINE_EMPTY(DWORD WINAPI GetModuleFileNameA_tramp(HMODULE,LPTSTR,DWORD));
DETOUR_TRAMPOLINE_EMPTY(DWORD WINAPI WritePrivateProfileStringA_tramp(LPCSTR,LPCSTR,LPCSTR, LPCSTR));
DETOUR_TRAMPOLINE_EMPTY(int __cdecl SendExeChecksum_Trampoline(void));
DETOUR_TRAMPOLINE_EMPTY(int __cdecl ProcessKeyDown_Trampoline(int));
DETOUR_TRAMPOLINE_EMPTY(int __cdecl ProcessKeyUp_Trampoline(int));
DETOUR_TRAMPOLINE_EMPTY(unsigned __int64 __stdcall GetCpuTicks2_Trampoline());
DETOUR_TRAMPOLINE_EMPTY(int __cdecl do_quit_Trampoline(int, int));
DETOUR_TRAMPOLINE_EMPTY(int __cdecl CityCanStart_Trampoline(int, int, int, int));
DETOUR_TRAMPOLINE_EMPTY(LRESULT WINAPI WndProc_Trampoline(HWND, UINT, WPARAM, LPARAM));
DETOUR_TRAMPOLINE_EMPTY(void WINAPI RightMouseDown_Trampoline(__int16, __int16));
DETOUR_TRAMPOLINE_EMPTY(void WINAPI RightMouseUp_Trampoline(__int16, __int16));
DETOUR_TRAMPOLINE_EMPTY(void WINAPI LeftMouseDown_Trampoline(__int16, __int16));
DETOUR_TRAMPOLINE_EMPTY(void WINAPI LeftMouseUp_Trampoline(__int16, __int16));
DETOUR_TRAMPOLINE_EMPTY(int Eqmachooks::CDisplay__Render_World_Trampoline());
DETOUR_TRAMPOLINE_EMPTY(int __cdecl  Eqmachooks::CDisplay__Process_Events_Trampoline());
DETOUR_TRAMPOLINE_EMPTY(HWND WINAPI CreateWindowExA_Trampoline(DWORD,LPCSTR,LPCSTR,DWORD,int,int,int,int,HWND,HMENU,HINSTANCE,LPVOID));
DETOUR_TRAMPOLINE_EMPTY(int __cdecl HandleMouseWheel_Trampoline(int));
DETOUR_TRAMPOLINE_EMPTY(int sub_4F35E5_Trampoline()); // command line parsing
DETOUR_TRAMPOLINE_EMPTY(int WINAPI sub_4B8231_Trampoline(int, signed int)); // MGB for BST
DETOUR_TRAMPOLINE_EMPTY(int Eqmachooks::CDisplay__StartWorldDisplay_Trampoline(int zoneindex, int x));

EQ_FUNCTION_TYPE_CBuffWindow__RefreshBuffDisplay  EQMACMQ_REAL_CBuffWindow__RefreshBuffDisplay = NULL;
EQ_FUNCTION_TYPE_CBuffWindow__PostDraw            EQMACMQ_REAL_CBuffWindow__PostDraw = NULL;
EQ_FUNCTION_TYPE_EQ_Character__CastSpell EQMACMQ_REAL_EQ_Character__CastSpell = NULL;

typedef int(__cdecl* EQ_FUNCTION_TYPE_CEverQuest__SendMessage)(int* connection, int opcode, char* buffer, size_t len, int unknown);
EQ_FUNCTION_TYPE_CEverQuest__SendMessage CEverQuest__SendMessage_Trampoline;
int __cdecl CEverQuest__SendMessage_Detour(int* connection, int opcode, char* buffer, size_t len, int unknown)
{
	if (opcode == 0x4092 && len >= 12) // OP_WearChange
	{
		if (Handle_Out_OP_WearChange((WearChange_Struct*)buffer))
			return 0;
	}
	return CEverQuest__SendMessage_Trampoline(connection, opcode, buffer, len, unknown);
}

class CCharacterSelectWnd;

class CCharacterSelectWnd : public CSidlScreenWnd
{
public:
	void CCharacterSelectWnd::Quit(void);
};

#define EQ_FUNCTION_CCharacterSelectWnd__Quit 0x0040F3E0
#ifdef EQ_FUNCTION_CCharacterSelectWnd__Quit
typedef int(__thiscall* EQ_FUNCTION_TYPE_CCharacterSelectWnd__Quit)(void* this_ptr);
#endif

EQ_FUNCTION_TYPE_CCharacterSelectWnd__Quit EQMACMQ_REAL_CCharacterSelectWnd__Quit = NULL;
EQ_FUNCTION_TYPE_CEverQuest__InterpretCmd EQMACMQ_REAL_CEverQuest__InterpretCmd = NULL;

int __fastcall EQMACMQ_DETOUR_CCharacterSelectWnd__Quit(void* this_ptr, void* not_used)
{
	// Quit or Esc button pressed from character select screen
	if (!bWindowedMode)
	{
		SetEQhWnd();
		SetWindowLong(EQhWnd, GWL_STYLE, stored_window_info.dwStyle | WS_CAPTION );
		SetWindowLong(EQhWnd, GWL_EXSTYLE, stored_window_info.dwExStyle & ~(WS_EX_TOPMOST));
#ifdef LOGGING
		WriteLog("EQGAME: Going Windowed - Quit from char select");
#endif
		can_fullscreen = false;
		bWindowedMode = true;
		start_fullscreen = true;
		first_maximize = true;
	}

	return EQMACMQ_REAL_CCharacterSelectWnd__Quit(this_ptr);
}

int __cdecl CEverQuest__DisplayScreen_Detour(char *a1) {
	// this is the "Client Disconnected" screen - go back to windowed
	if (!bWindowedMode) {
		SetEQhWnd();
		SetWindowLong(EQhWnd, GWL_STYLE, stored_window_info.dwStyle | WS_CAPTION );
		SetWindowLong(EQhWnd, GWL_EXSTYLE, stored_window_info.dwExStyle & ~(WS_EX_TOPMOST));
#ifdef LOGGING
		WriteLog("EQGAME: Dropping to Windowed Mode - Client Disconnected");
#endif
		can_fullscreen = false;
		bWindowedMode = true;
		start_fullscreen = true;
		first_maximize = true;
	}

	return CEverQuest__DisplayScreen_Trampoline(a1);
}

LRESULT WINAPI WndProc_Detour(HWND hWnd, UINT Msg, WPARAM wParam, LPARAM lParam) {
	if (EQ_OBJECT_CEverQuest != NULL && Msg != 16) {

		if (WM_WINDOWPOSCHANGED == Msg || WM_WINDOWPOSCHANGING == Msg || WM_NCCALCSIZE == Msg || WM_PAINT == Msg)
		{
			return 0;
		}
		
		if (WM_SYSCOMMAND == Msg)
		{
			if (wParam == SC_MINIMIZE)
			{
				return 0;
			}
		}
		
		if (WM_ACTIVATE == Msg || WM_ACTIVATEAPP == Msg)
		{
			if (wParam) {
				SetEQhWnd();
				//if (in_full_screen)
				//	start_fullscreen = true;
				//else
					 ShowWindow(EQhWnd, SW_SHOW);
				
				ResetMouseFlags();
				while (ShowCursor(FALSE) >= 0);
			}
			else
			{
				ResetMouseFlags();
				while (ShowCursor(TRUE) < 0);
			}
		}

		if (!bWindowedMode || start_fullscreen) {
			SetEQhWnd();
			if (EQ_OBJECT_CEverQuest->GameState > 0 && EQ_OBJECT_CEverQuest->GameState != 255 && can_fullscreen) {
				if (start_fullscreen && bWindowedMode && !IsIconic(EQhWnd)) {
					// this does not hit initially on startup
#ifdef LOGGING
					WriteLog("EQGAME: Going Fullscreen (3)");
#endif
					if (bWindowedMode && !window_info_stored) {
#ifdef LOGGING
						WriteLog("EQGAME: Storing window info");
#endif
						GetWindowInfo(EQhWnd, &stored_window_info);
						window_info_stored = true;
					}

					stored_window_info.dwStyle = GetWindowLong(EQhWnd, GWL_STYLE);
					stored_window_info.dwExStyle = GetWindowLong(EQhWnd, GWL_EXSTYLE);

					SetWindowLong(EQhWnd, GWL_STYLE,
						stored_window_info.dwStyle & ~(WS_CAPTION | WS_THICKFRAME | WS_SYSMENU));

					SetWindowLong(EQhWnd, GWL_EXSTYLE,
						stored_window_info.dwExStyle & ~(WS_EX_DLGMODALFRAME |
							WS_EX_WINDOWEDGE | WS_EX_CLIENTEDGE | WS_EX_STATICEDGE));

					MONITORINFO monitor_info;
					monitor_info.cbSize = sizeof(monitor_info);
					GetMonitorInfo(MonitorFromWindow(EQhWnd, MONITOR_DEFAULTTONEAREST),
						&monitor_info);
					RECT window_rect(monitor_info.rcMonitor);

					WINDOWPLACEMENT window_placement;
					window_placement.length = sizeof(window_placement);

					if (first_maximize) {
						GetWindowPlacement(EQhWnd, &window_placement);
						window_placement.showCmd = SW_MINIMIZE;
						SetWindowPlacement(EQhWnd, &window_placement);
						window_placement.showCmd = SW_MAXIMIZE;
						SetWindowPlacement(EQhWnd, &window_placement);
					}
					if (!IsIconic(EQhWnd) && window_info_stored) {
						SetWindowPos(EQhWnd, HWND_TOP, window_rect.left, window_rect.top,
							window_rect.right - window_rect.left, window_rect.bottom - window_rect.top,
							SWP_NOOWNERZORDER | SWP_FRAMECHANGED | SWP_NOSENDCHANGING | SWP_SHOWWINDOW);
					}

					bWindowedMode = false;		
					first_maximize = false;
				}
			}
		}
	}
	else {
		if (!bWindowedMode) {
			//MessageBox(NULL, "C3", NULL, MB_OK);
#ifdef LOGGING
			WriteLog("EQGAME: Dropping Fullscreen (2)");
#endif
			SetWindowLong(EQhWnd, GWL_STYLE, stored_window_info.dwStyle | WS_CAPTION );
			SetWindowLong(EQhWnd, GWL_EXSTYLE, stored_window_info.dwExStyle | WS_EX_APPWINDOW);

			if (!IsIconic(EQhWnd) && window_info_stored) {
				SetWindowPos(EQhWnd, HWND_TOP, stored_window_info.rcWindow.left, stored_window_info.rcWindow.top,
					stored_window_info.rcWindow.right - stored_window_info.rcWindow.left, stored_window_info.rcWindow.bottom - stored_window_info.rcWindow.top,
					SWP_NOOWNERZORDER | SWP_FRAMECHANGED | SWP_NOSENDCHANGING | SWP_SHOWWINDOW);
			}
			can_fullscreen = false;
			bWindowedMode = true;
			start_fullscreen = true;
			first_maximize = true;
		}
		if (!title_set) {
			UpdateTitle();
			title_set = true;
		}
	}
	LRESULT res = WndProc_Trampoline(hWnd, Msg, wParam, lParam);
	return res;
}

void SkipLicense()
{
	DWORD offset = (DWORD)eqmain_dll + 0x255D2;
	const char test1[] = { 0xEB }; // , 0x90, 0x90, 0x90, 0x90, 0x90};
	PatchA((DWORD*)offset, &test1, sizeof(test1));
}

void SkipSplash()
{
	// Set timer for intro splash screens to 0
	const char test1[] = { 0x00, 0x00 };

	DWORD offset = (DWORD)eqmain_dll + 0x21998;
	PatchA((DWORD*)offset, &test1, sizeof(test1));
}

void SetDInputCooperativeMode()
{
	// Set timer for intro splash screens to 0
	const char test1[] = { (char)(0x06) };

	DWORD offset = (DWORD)eqmain_dll + 0x3400F;
	PatchA((DWORD*)offset, &test1, sizeof(test1));
}

//#ifdef GM_MODE
void __fastcall EQMACMQ_DETOUR_CBuffWindow__RefreshBuffDisplay(CBuffWindow* this_ptr, void* not_used)
{

	PEQCBUFFWINDOW buffWindow = (PEQCBUFFWINDOW)this_ptr;
	PEQCHARINFO charInfo = (PEQCHARINFO)EQ_OBJECT_CharInfo;

	if (charInfo == NULL)
	{
		return;
	}

	// Supports ShortBuffWindow(Songs) and BuffWindow, which use different buff offsets
	bool is_song_window = (this_ptr == GetShortDurationBuffWindow());
	_EQBUFFINFO* buffs = GetStartBuffArray(is_song_window);

	MakeGetBuffReturnSongs(is_song_window);
	EQMACMQ_REAL_CBuffWindow__RefreshBuffDisplay(this_ptr);
	MakeGetBuffReturnSongs(false);

	int num_buffs = 0;

	// -- Standard Dll Support Buff Text / Timer --
	for (size_t i = 0; i < EQ_NUM_BUFFS; i++)
	{
		EQBUFFINFO& buff = buffs[i];
		if (!EQ_Spell::IsValidSpellIndex(buff.SpellId) || buff.BuffType == 0)
		{
			continue;
		}
		num_buffs++;

		int buffTicks = buff.Ticks;

		if (buffTicks == 0)
		{
			continue;
		}

		PEQCBUFFBUTTONWND buffButtonWnd = buffWindow->BuffButtonWnd[i];

		if (buffButtonWnd && buffButtonWnd->CSidlWnd.EQWnd.ToolTipText)
		{
			char buffTickTimeText[128];
			EQ_GetTickTimeString(buffTicks, buffTickTimeText, sizeof(buffTickTimeText));

			char buffTimeText[128];
			_snprintf_s(buffTimeText, sizeof(buffTimeText), _TRUNCATE, " (%s)", buffTickTimeText);

			EQ_CXStr_Append(&buffButtonWnd->CSidlWnd.EQWnd.ToolTipText, buffTimeText);
		}
	}

	if (is_song_window)
	{
		if (this_ptr->IsVisibile())
		{
			if (num_buffs == 0 && (g_bSongWindowAutoHide || Rule_Num_Short_Buffs == 0)) // Visible, but support is disabled or auto-hide
				this_ptr->Show(0, 1);
			return;
		}
		if (num_buffs > 0)
		{
			// Not visible and we have buffs. Show.
			this_ptr->Show(1, 1);
		}
	}
}

int __fastcall EQMACMQ_DETOUR_EQ_Character__CastSpell(void* this_ptr, void* not_used, unsigned char a1, short a2, EQITEMINFO** a3, short a4)
{
	PEQSPAWNINFO playerSpawn = (PEQSPAWNINFO)EQ_OBJECT_PlayerSpawn;

	if (playerSpawn != NULL)
	{
		if (playerSpawn->StandingState == EQ_STANDING_STATE_SITTING)
		{
			((EQPlayer*)playerSpawn)->ChangePosition(EQ_STANDING_STATE_STANDING);
		}
	}

	return EQMACMQ_REAL_EQ_Character__CastSpell(this_ptr, a1, a2, a3, a4);
}

int __fastcall EQMACMQ_DETOUR_CBuffWindow__PostDraw(CBuffWindow* this_ptr, void* not_used)
{

	int result = EQMACMQ_REAL_CBuffWindow__PostDraw(this_ptr);

	PEQCBUFFWINDOW buffWindow = (PEQCBUFFWINDOW)this_ptr;

	PEQCHARINFO charInfo = (PEQCHARINFO)EQ_OBJECT_CharInfo;

	if (charInfo == NULL)
	{
		return result;
	}

	bool is_song_window = (this_ptr == GetShortDurationBuffWindow());
	_EQBUFFINFO* buffs = GetStartBuffArray(is_song_window); // Song Window Support

	for (size_t i = 0; i < EQ_NUM_BUFFS; i++)
	{
		EQBUFFINFO& buff = buffs[i];
		if (!EQ_Spell::IsValidSpellIndex(buff.SpellId) || buff.BuffType == 0)
		{
			continue;
		}

		int buffTicks = buff.Ticks;
		if (buffTicks == 0)
		{
			continue;
		}

		char buffTimeText[128];
		EQ_GetShortTickTimeString(buffTicks, buffTimeText, sizeof(buffTimeText));

		PEQCBUFFBUTTONWND buffButtonWnd = buffWindow->BuffButtonWnd[i];

		if (buffButtonWnd && buffButtonWnd->CSidlWnd.EQWnd.ToolTipText)
		{
			buffButtonWnd->CSidlWnd.EQWnd.FontPointer->Size = g_buffWindowTimersFontSize;

			char originalToolTipText[128];
			strncpy_s(originalToolTipText, sizeof(originalToolTipText), buffButtonWnd->CSidlWnd.EQWnd.ToolTipText->Text, _TRUNCATE);

			EQ_CXStr_Set(&buffButtonWnd->CSidlWnd.EQWnd.ToolTipText, buffTimeText);

			CXRect relativeRect = ((CXWnd*)buffButtonWnd)->GetScreenRect();

			((CXWnd*)buffButtonWnd)->DrawTooltipAtPoint(relativeRect.X1, relativeRect.Y1);

			EQ_CXStr_Set(&buffButtonWnd->CSidlWnd.EQWnd.ToolTipText, originalToolTipText);

			buffButtonWnd->CSidlWnd.EQWnd.FontPointer->Size = EQ_FONT_SIZE_DEFAULT;
		}
	}

	return result;
}

void EQMACMQ_DoMouseWheelZoom(int mouseWheelDelta)
{
	PEQSPAWNINFO playerSpawn = (PEQSPAWNINFO)EQ_OBJECT_PlayerSpawn;

	if (playerSpawn == NULL)
		return;

	float g_mouseWheelZoomMultiplier = 0.44f;

	float g_minZoom = playerSpawn->ModelHeightOffset * g_mouseWheelZoomMultiplier;

	if (g_minZoom < 2.0f)
		g_minZoom = 2.0f;

	DWORD cameraView = EQ_ReadMemory<DWORD>(EQ_CAMERA_VIEW);

	FLOAT cameraThirdPersonZoom = 0.0f;

	FLOAT cameraThirdPersonZoomMax = EQ_ReadMemory<FLOAT>(EQ_CAMERA_VIEW_THIRD_PERSON_ZOOM_MAX);

	float zoom = 0.0f;

	DWORD zoomAddress = NULL;

	if (cameraView == EQ_CAMERA_VIEW_THIRD_PERSON2)
	{
		cameraThirdPersonZoom = EQ_ReadMemory<FLOAT>(EQ_CAMERA_VIEW_THIRD_PERSON2_ZOOM);

		zoomAddress = EQ_CAMERA_VIEW_THIRD_PERSON2_ZOOM;
	}
	else if (cameraView == EQ_CAMERA_VIEW_THIRD_PERSON3)
	{
		cameraThirdPersonZoom = EQ_ReadMemory<FLOAT>(EQ_CAMERA_VIEW_THIRD_PERSON3_ZOOM);

		zoomAddress = EQ_CAMERA_VIEW_THIRD_PERSON3_ZOOM;
	}
	else if (cameraView == EQ_CAMERA_VIEW_THIRD_PERSON4)
	{
		cameraThirdPersonZoom = EQ_ReadMemory<FLOAT>(EQ_CAMERA_VIEW_THIRD_PERSON4_ZOOM);

		zoomAddress = EQ_CAMERA_VIEW_THIRD_PERSON4_ZOOM;
	}

	if (mouseWheelDelta == EQ_MOUSE_WHEEL_DELTA_UP)
	{
		if
			(
				cameraView == EQ_CAMERA_VIEW_THIRD_PERSON2 ||
				cameraView == EQ_CAMERA_VIEW_THIRD_PERSON3 ||
				cameraView == EQ_CAMERA_VIEW_THIRD_PERSON4
				)
		{
			if (cameraThirdPersonZoom <= g_minZoom)
			{
				if (cameraView == EQ_CAMERA_VIEW_THIRD_PERSON2)
				{
					EQ_WriteMemory<DWORD>(EQ_CAMERA_VIEW, EQ_CAMERA_VIEW_FIRST_PERSON);
				}
				else
				{
					if (zoomAddress != NULL)
					{
						zoom = g_minZoom;

						EQ_WriteMemory<FLOAT>(zoomAddress, zoom);
					}
				}
			}
			else
			{
				if (zoomAddress != NULL)
				{
					zoom = cameraThirdPersonZoom - (playerSpawn->ModelHeightOffset * g_mouseWheelZoomMultiplier);

					if (zoom < g_minZoom)
					{
						zoom = g_minZoom;
					}

					EQ_WriteMemory<FLOAT>(zoomAddress, zoom);
				}
			}
		}
	}
	else if (mouseWheelDelta == EQ_MOUSE_WHEEL_DELTA_DOWN)
	{
		if (cameraView == EQ_CAMERA_VIEW_FIRST_PERSON)
		{
			zoom = g_minZoom;

			EQ_WriteMemory<FLOAT>(EQ_CAMERA_VIEW_THIRD_PERSON2_ZOOM, zoom);

			EQ_WriteMemory<DWORD>(EQ_CAMERA_VIEW, EQ_CAMERA_VIEW_THIRD_PERSON2);
		}
		else if
			(
				cameraView == EQ_CAMERA_VIEW_THIRD_PERSON2 ||
				cameraView == EQ_CAMERA_VIEW_THIRD_PERSON3 ||
				cameraView == EQ_CAMERA_VIEW_THIRD_PERSON4
				)
		{
			if (zoomAddress != NULL)
			{
				zoom = cameraThirdPersonZoom + (playerSpawn->ModelHeightOffset * g_mouseWheelZoomMultiplier);

				if (zoom > cameraThirdPersonZoomMax)
				{
					zoom = cameraThirdPersonZoomMax;
				}

				EQ_WriteMemory<FLOAT>(zoomAddress, zoom);
			}
		}
	}
}
//#endif

// MGB for BST
int WINAPI sub_4B8231_Detour(int a1, signed int a2) {
	if (a1 == 15 && a2 == 35)
		return 1;
	return sub_4B8231_Trampoline(a1, a2);
}

// command line parsing
int sub_4F35E5_Detour(){

		const char*v3;
		int v22;
		char exename[256];
		v3 = GetCommandLineA();
		*(int*)0x00809464 = sscanf(
			v3,
			"%s %s %s %s %s %s %s %s %s",
			&exename,
			(char*)0x806410,
			(char*)0x806510,
			(char*)0x806610,
			(char*)0x806710,
			(char*)0x806810,
			(char*)0x806910,
			(char*)0x806A10,
			(char*)0x806B10);

		DWORD v59 = 0;
		int v20 = 0x00806410;

		if (*(DWORD*)0x00809464 > 1)
		{
			while (1)
			{
				v22 = strlen((const char *)v20);
				if (v22 + strlen((char *)0x00807B08) + 2 < 0x1C0)
				{
					strcat((char *)0x00807B08, (const char *)v20);
					strcat((char *)0x00807B08, " ");
				}
				if (!_strnicmp((const char *)v20, "nosound.txt", 5u))
					break;

				if (!_strnicmp((const char *)v20, "/ticket:", 8u))
				{
					char ticket_[63];
					strncpy(ticket_, (const char *)(v20 + 8), 0x3Fu);
					if (strlen(ticket_) > 1 && ticket_[strlen(ticket_) - 1] == 34)
						ticket_[strlen(ticket_)-1] = 0;

					// original code
					// strncpy((char *)0x00807D48, ticket_, 0x3Fu);
					// MessageBox(NULL, ticket_, NULL, MB_OK);

					// replacement code
					std::string userpass = ticket_;

					std::string username = userpass.substr(0, userpass.find("/"));
					std::string password = userpass.substr(userpass.find("/") + 1);

					if (username.length() > 3 && password.length() > 3) {
						strcpy((char *)0x807AC8, username.c_str()); // username
						strcpy((char *)0x807924, password.c_str()); // password = > likely needs encrypted pass?
					}
				}
				else if (!_strnicmp((const char *)v20, "/title:", 7u))
				{
					char my_title[63];
					strncpy(my_title, (const char *)(v20 + 7), 0x7Fu);
					if (strlen(my_title) > 1)
						new_title = my_title;
				}

				++v59;
				v20 += 256;
				if (v59 >= *(DWORD*)0x00809464)
					break;
			}

		}

	return sub_4F35E5_Trampoline();
}

extern bool mouse_looking;
extern POINT savedRMousePos;

void WINAPI RightMouseUp_Detour(__int16 a1, __int16 a2) {
	if (ignore_right_click_up)
		return;

	return RightMouseUp_Trampoline(a1, a2);
}

void WINAPI RightMouseDown_Detour(__int16 a1, __int16 a2) {

	if (ignore_right_click) {
		if (!(GetAsyncKeyState(VK_RBUTTON) & 0x8000)) {
			if (has_focus && focus_regained_time > 0) {
				if ((GetTickCount() - focus_regained_time) > 10) {
					ignore_right_click_up = false;
					ignore_right_click = false;
					ignore_left_click_up = false;
					ignore_left_click = false;
					focus_regained_time = 0;
				}
				else {
					ignore_right_click_up = true;
					return;
				}
			}
			else {
				ignore_right_click_up = true;
				return;
			}
		}
		else {
			ignore_right_click = false;
			ignore_right_click_up = false;
		}
	}

	RightMouseDown_Trampoline(a1, a2);
	if(EQ_OBJECT_CEverQuest != NULL && EQ_OBJECT_CEverQuest->GameState == 5) {
		if (*(DWORD*)0x007985EA == 0x00010001) {
			mouse_looking = true;
			if (savedRMousePos.x == 0 && savedRMousePos.y == 0)
			{
				savedRMousePos.x = *(DWORD*)0x008092E8;
				savedRMousePos.y = *(DWORD*)0x008092EC;
			}
		}
	}
	return;
}

void WINAPI LeftMouseUp_Detour(__int16 a1, __int16 a2) {
	if (ignore_left_click_up)
		return;

	return LeftMouseUp_Trampoline(a1, a2);
}

void WINAPI LeftMouseDown_Detour(__int16 a1, __int16 a2) {

	if (ignore_left_click) {
		if (!(GetAsyncKeyState(VK_LBUTTON) & 0x8000)) {
			if (has_focus && focus_regained_time > 0) {
				if ((GetTickCount() - focus_regained_time) > 10) {
					ignore_left_click_up = false;
					ignore_left_click = false;
					ignore_right_click_up = false;
					ignore_right_click = false;
					focus_regained_time = 0;
				}
				else {
					ignore_left_click_up = true;
					return;
				}
			}
			else {
				ignore_left_click_up = true;
				return;
			}
		}
		else {
			ignore_left_click = false;
			ignore_left_click_up = false;
		}
	}
	return LeftMouseDown_Trampoline(a1, a2);
}

int __cdecl HandleMouseWheel_Detour(int a1) {
	// do mouse wheel only if in game
	if (EQ_OBJECT_CEverQuest != NULL && can_fullscreen && EQ_OBJECT_CEverQuest->GameState == 5) {
		// add check here to see if GM
		PEQSPAWNINFO playerSpawn = (PEQSPAWNINFO)EQ_OBJECT_PlayerSpawn;
		if (playerSpawn == NULL)
			return HandleMouseWheel_Trampoline(a1);
		
		if (EQ_IsMouseHoveringOverCXWnd() == true)
		{
			return HandleMouseWheel_Trampoline(a1);
		}
		EQMACMQ_DoMouseWheelZoom(a1);

		if (!*(BYTE*)0x8092D8);
			return 0;
	}
	return HandleMouseWheel_Trampoline(a1);
}

void PatchSaveBypass()
{
	//const char test1[] =  { 0xEB, 0x21 };
	//PatchA((DWORD*)0x0052B70A, &test1, sizeof(test1));
	const char test1[] = { 0x00, 0x00 };
	PatchA((DWORD*)0x0052B716, &test1, sizeof(test1));
	// OP_Save
	// this stops sending OP_SAVE
	//const char test2[] = { 0x90, 0x90, 0x90, 0x90, 0x90 };
	//PatchA((DWORD*)0x00536797, &test2, sizeof(test2));
	// this forces sending OP_SAVE with size of 0.
	const char test2[] = { 0x00, 0x00 };
	PatchA((DWORD*)0x0053678C, &test2, sizeof(test2));

	//SetCooperativeLevel to 0x06 instead of 0x10 for eqgame.exe
	//const char test3[] = { 0x06 };
	//PatchA((DWORD*)0x0055B844, &test3, sizeof(test3));

	// Inverse NewUI flags for OldUI naming
	//const char test4[] = { 0x00 };
	//PatchA((DWORD*)0x00559866, &test4, sizeof(test4));
	//
	//// Inverse NewUI flags for OldUI naming
	//const char test5[] = { 0x00 };
	//PatchA((DWORD*)0x005598C1, &test5, sizeof(test5));

	//// Inverse NewUI flags for OldUI naming
	//const char test6[] = { 0x01 };
	//PatchA((DWORD*)0x005598CB, &test6, sizeof(test6));

	//// Change name of setting: NewUI -> OldUI
	//const char test7[] = { 0x4F, 0x6C, 0x64 /*"Old"*/ };
	//PatchA((DWORD*)0x0060DB1C, &test7, sizeof(test7));

	//// Change name of command: /newui -> /oldui
	//const char test8[] = { 0x6F, 0x6C, 0x64 /*"old"*/ };
	//PatchA((DWORD*)0x0060B6E8, &test8, sizeof(test8));

	//// Change string of command /oldui to match functionality:
	//const char test9[] = { 0xA5 };
	//PatchA((DWORD*)0x4FFAC2, &test9, sizeof(test9));
	//
	//// Change string of command /oldui to match functionality:
	//const char test10[] = { 0xA4 };
	//PatchA((DWORD*)0x4FFAE0, &test10, sizeof(test10));

	//// Inverse NewUI flags for OldUI naming
	//const char test11[] = { 0xC6, 0x05 };
	//PatchA((DWORD*)0x005598C5, &test11, sizeof(test11));

	// Face picker patch.
	const char test12[] = { 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0xEB };
	PatchA((DWORD*)0x005431C1, &test12, sizeof(test12));

	if (g_bEnableBrownSkeletons)
	{
		const char test13[] = { 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0xEB };
		PatchA((DWORD*)0x0049F28F, &test13, sizeof(test13));
	}

	const char test14[] = { 0xEB, 0x1A };
	PatchA((DWORD*)0x42D14D, &test14, sizeof(test14));

	//Changes the limit to 0x3E8 (1000) on race animations.
	const char test15[] = { 0xE8, 0x03 };
	PatchA((DWORD*)0x004AE612, &test15, sizeof(test15));

	//Changes the limit to 0x3E8 (1000) on race animations.
	const char test16[] = { 0xE8, 0x03 };
	PatchA((DWORD*)0x4d93c5, &test16, sizeof(test16));

	//Changes the limit to 0x3E8 (1000) on race spawning to apply sounds and textures.
	const char test17[] = { 0xE8, 0x03 };
	PatchA((DWORD*)0x50704c, &test17, sizeof(test17));

	////Patch the trampoline for untextured horse to check its validity. currently hardcoded to IDs in hook, but this bypasses the initial check. 11 nops.
	//const char test18[] = { 0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90 };
	//PatchA((DWORD*)0x51FC6D, &test18, sizeof(test18));
	//PatchA((DWORD*)0x4AFA02, &test18, sizeof(test18));
	//PatchA((DWORD*)0x51FE08, &test18, sizeof(test18));
	//PatchA((DWORD*)0x51FDE6, &test18, sizeof(test18));
	//PatchA((DWORD*)0x51FE86, &test18, sizeof(test18));
	////Patch the check for Horse ID to allow for more IDs than just 216. 15 nops.
	//const char test19[] = { 0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90,0x90 };
	//PatchA((DWORD*)0x4B07D7, &test19, sizeof(test19));
}

typedef int(__cdecl *_s3dSetStringSpriteYonClip)(intptr_t, int, float);
_s3dSetStringSpriteYonClip s3dSetStringSpriteYonClip_Trampoline;
int __cdecl s3dSetStringSpriteYonClip_Detour(intptr_t sprite, int a2, float distance)
{
	//Log("s3dSetStringSpriteYonClip_Detour 0x%lx %d %f", sprite, a2, distance);
	if (g_bEnableExtendedNameplates == false)
		return s3dSetStringSpriteYonClip_Trampoline(sprite, a2, distance);

	if ((*(unsigned int *)&distance) == 0x428c0000) // 70.0f
	{
		a2 = 0;
		//distance = 1000.0f;
	}

	return s3dSetStringSpriteYonClip_Trampoline(sprite, a2, distance);
}



typedef unsigned __int64(__cdecl *_GetCpuSpeed2)();
typedef float (__cdecl *_FastMathFunction)(float);
typedef float(__cdecl *_CalculateAccurateCoefficientsFromHeadingPitchRoll)(float, float, float, float);

typedef float(__cdecl *_FastAngleArcFunction)(DWORD, DWORD, DWORD);

_FastMathFunction GetFastCosine_Trampoline;
_FastMathFunction GetFastSine_Trampoline;
_FastMathFunction GetFastCotangent_Trampoline;
_CalculateAccurateCoefficientsFromHeadingPitchRoll CalculateCoefficientsFromHeadingPitchRoll_Trampoline;
_CalculateAccurateCoefficientsFromHeadingPitchRoll CalculateHeadingPitchRollFromCoefficients_Trampoline;
_FastAngleArcFunction GetFactAngleArcFunction;
_GetCpuSpeed2 GetCpuSpeed1_Trampoline;
_GetCpuSpeed2 GetCpuSpeed2_Trampoline;
_GetCpuSpeed2 GetCpuSpeed3_Trampoline;

LARGE_INTEGER g_ProcessorSpeed;
LARGE_INTEGER g_ProcessorTicks;

unsigned __int64 __stdcall GetCpuTicks_Detour() {

	LARGE_INTEGER qpcResult;
	QueryPerformanceCounter(&qpcResult);
	return (qpcResult.QuadPart - g_ProcessorTicks.QuadPart);
}

unsigned __int64 __stdcall GetCpuSpeed2_Detour() {
		LARGE_INTEGER Frequency;

		if (!QueryPerformanceFrequency(&Frequency))
		{
			MessageBoxW(0, L"This OS is not supported.", L"Error", 0);
			exit(-1);
		}
		g_ProcessorSpeed.QuadPart = Frequency.QuadPart / 1000;
		QueryPerformanceCounter(&g_ProcessorTicks);
		Sleep(1000u);
		return g_ProcessorSpeed.QuadPart;
}

DWORD org_nonFastCos = 0;
DWORD org_nonFastSin = 0;
DWORD org_nonFastCotangent = 0;
DWORD org_fix16Tangent = 0;
DWORD org_calculateAccurateCoefficientsFromHeadingPitchRoll = 0;
DWORD org_calculateAccurateHeadingPitchRollFromCoefficients = 0;
float __cdecl t3dFastCosine_Detour(float a1) {

	if (org_nonFastCos)
	{
		return ((float (__cdecl*) (float)) org_nonFastCos)(a1);
	}

	return GetFastCosine_Trampoline(a1);
}

float __cdecl t3dFastSine_Detour(float a1) {

	if (org_nonFastSin)
	{
		return ((float(__cdecl*) (float)) org_nonFastSin)(a1);
	}

	return GetFastSine_Trampoline(a1);
}

float __cdecl t3dFastCotangent_Detour(float a1) {

	if (org_nonFastCotangent)
	{
		return ((float(__cdecl*) (float)) org_nonFastCotangent)(a1);
	}

	return GetFastCotangent_Trampoline(a1);
}

float CalculateCoefficientsFromHeadingPitchRoll_Detour(float a1, float a2, float a3, float a4) {

	if (org_calculateAccurateCoefficientsFromHeadingPitchRoll)
	{
		return ((float(__cdecl*) (float, float, float, float))org_calculateAccurateCoefficientsFromHeadingPitchRoll)(a1, a2, a3, a4);
	}

	return CalculateCoefficientsFromHeadingPitchRoll_Trampoline(a1, a2, a3, a4);
}

float CalculateHeadingPitchRollFromCoefficients_Detour(float a1, float a2, float a3, float a4) {

	if (org_calculateAccurateHeadingPitchRollFromCoefficients)
	{
		return ((float(__cdecl*) (float, float, float, float))org_calculateAccurateHeadingPitchRollFromCoefficients)(a1, a2, a3, a4);
	}

	return CalculateHeadingPitchRollFromCoefficients_Trampoline(a1, a2, a3, a4);
}

//float __cdecl t3dAngleArcTangentFloat_Detour(DWORD a1, DWORD a2, DWORD a3) {
//
//	if (org_fix16Tangent)
//	{
//		return ((float(__cdecl*) (float)) org_fix16Tangent)(a1);
//	}
//
//	return t3dAngleArcTangentFloat_Trampoline(a1);
//}



HWND WINAPI CreateWindowExA_Detour(DWORD     dwExStyle,
	LPCSTR   lpClassName,
	LPCSTR   lpWindowName,
	DWORD     dwStyle,
	int       x,
	int       y,
	int       nWidth,
	int       nHeight,
	HWND      hWndParent,
	HMENU     hMenu,
	HINSTANCE hInstance,
	LPVOID    lpParam) {

	can_fullscreen = false;
	first_maximize = true;
	if (!eqmain_dll) {
		eqmain_dll = GetModuleHandleA("eqmain.dll");
		if (eqmain_dll) {
			DWORD checkpoint = *(DWORD*)0x807410;
			DWORD delta = checkpoint - (DWORD)eqmain_dll;
			// if new_main_dll is at right location in dll
			// then add bypass for skipping license and splash screen
			if (delta == 0x25300) {
				//SkipLicense();
				if(g_bEnableExtendedNameplates)
				{
					//g_ProcessorSpeed = 0;
				}
				(_GetCpuSpeed2)GetCpuSpeed3_Trampoline = (_GetCpuSpeed2)DetourFunction((PBYTE)0x00559BF4, (PBYTE)GetCpuTicks_Detour);
				//(_GetCpuSpeed2)GetCpuSpeed2_Trampoline = (_GetCpuSpeed2)DetourFunction((PBYTE)0x00559BF4, (PBYTE)GetCpuSpeed2_Detour);
				//PatchA((DWORD*)0x007812F8, &g_ProcessorSpeed, 8);
				SkipSplash();
				//SetDInputCooperativeMode();
			}
			PatchSaveBypass();
		}
	}
	return CreateWindowExA_Trampoline(dwExStyle, lpClassName, lpWindowName, dwStyle, x, y, nWidth, nHeight, hWndParent, hMenu, hInstance, lpParam);
}

int __cdecl do_quit_Detour(int a1, int a2) {
	if (!a2 || !*(BYTE *)a2)
	{
		if (*(BYTE*)0x7CF29C)
		{
			// we are locked
		}
		else {
			// Quit or Esc button pressed from character select screen
			if (!bWindowedMode)
			{
				SetEQhWnd();
				SetWindowLong(EQhWnd, GWL_STYLE, stored_window_info.dwStyle | WS_CAPTION );
				SetWindowLong(EQhWnd, GWL_EXSTYLE, stored_window_info.dwExStyle & ~(WS_EX_TOPMOST));
#ifdef LOGGING
				WriteLog("EQGAME: Going Windowed - Used /quit from in game");
#endif
				can_fullscreen = false;
				bWindowedMode = true;
				start_fullscreen = true;
				first_maximize = true;
			}
		}
	}
	return do_quit_Trampoline(a1, a2);
}
typedef int(__thiscall* EQ_FUNCTION_TYPE_EQPlayer__LegalPlayerRace)(void* this_ptr, int a3);
EQ_FUNCTION_TYPE_EQPlayer__LegalPlayerRace LegalPlayerRace_Trampoline;
int __fastcall LegalPlayerRace_Detour(void* this_ptr, void* not_used, int a3) {
	//if (a3 == 26)
	//{
	//	return 1;
	//}
	return LegalPlayerRace_Trampoline(this_ptr, a3);
}

// --------------------------------------------------------------------------
// Legacy Model Horse Support
// --------------------------------------------------------------------------

// Cache of which races have a RIDER_DAG
std::map<WORD, bool> is_horse_map;

thread_local WORD ActualHorseRaceID = 0;

unsigned short GetActualHorseRaceID(_EQSPAWNINFO* entity)
{
	if (entity->Race == 216 && ActualHorseRaceID)
		return ActualHorseRaceID;
	return entity->Race;
}

EQDAGINFO* GetHeirarchicalSpriteDagByName(EQMODELINFO* sprite, char* dag_name)
{
	return reinterpret_cast<EQDAGINFO*(__cdecl*)(EQMODELINFO*, char*)>(*(int*)0x7F9A0C)(sprite, dag_name);
}

EQDAGINFO* GetRiderDag(EQSPAWNINFO* entity)
{
	if (!entity || !entity->ActorInfo || !entity->ActorInfo->ModelInfo || entity->ActorInfo->ModelInfo->Type != 20)
		return nullptr;

	char tag_name[8];
	memset(tag_name, 0, sizeof(tag_name));
	char dag_name[32];
	memset(dag_name, 0, sizeof(dag_name));

	reinterpret_cast<int(__thiscall*)(EQSPAWNINFO*,char*)>(0x50845D)(entity, tag_name); // GetActorTag(entity, buf)
	sprintf(dag_name, "%sRIDER_DAG", tag_name);
	EQDAGINFO* dag = GetHeirarchicalSpriteDagByName(entity->ActorInfo->ModelInfo, dag_name);
#ifdef HORSE_LOGGING
	print_chat("%s %s for race %u modeltype %u", dag_name, dag ? "found" : "not found", entity->Race, entity->ActorInfo->ModelInfo->Type);
#endif
	return dag;
}

// Replaced the basic EQ IsHorse() function which only checks Race == 216
bool __fastcall IsHorse(EQSPAWNINFO* entity, int unused)
{
	if (!entity)
		return false;

	WORD race = entity->Race;
	switch (race)
	{
	case 0: // none
	case 1: // hum
	case 2: // bar
	case 3: // eru
	case 4: // elf
	case 5: // hie
	case 6: // def
	case 7: // hef
	case 8: // dwaf
	case 9: // trol
	case 10: // ogr
	case 11: // hlf
	case 12: // gnm
	case 26: // frg
	case 27: // frg
	case 128: // isk
	case 130: // vah
		return false;
	case 216: // horse
		return true;
	}

	auto it = is_horse_map.find(race);
	if (it != is_horse_map.end())
		return it->second;

	// Cache the result
	bool is_horse = GetRiderDag(entity) != nullptr;
	is_horse_map[race] = is_horse;
	return is_horse;
}

bool FakeHorseRace(EQSPAWNINFO* entity)
{
	if (entity && entity->Race != 216 && IsHorse(entity, 0))
	{
		ActualHorseRaceID = entity->Race;
		entity->Race = 216;
		return true;
	}
	return false;
}

void UnFakeHorseRace(EQSPAWNINFO* entity, bool faked)
{
	if (faked)
	{
		if (!entity)
		{
			// it despawned
			ActualHorseRaceID = 0;
#ifdef HORSE_LOGGING
			print_chat("Custom Horse Despawned");
#endif
		}
		else if (entity->Race == 216 && ActualHorseRaceID)
		{
			entity->Race = ActualHorseRaceID;
			ActualHorseRaceID = 0;
		}
		else
		{
#ifdef HORSE_LOGGING
			print_chat("Invalid state for UnFakeHorseRace Race %u TheadLocal %u", entity->Race, ActualHorseRaceID);
#endif
		}
	}
}

typedef int(__thiscall* EQ_FUNCTION_TYPE_EQPlayer__HasInvalidRiderTexture)(void* this_ptr);
EQ_FUNCTION_TYPE_EQPlayer__HasInvalidRiderTexture HasInvalidRiderTexture_Trampoline;
int __fastcall HasInvalidRiderTexture_Detour(EQSPAWNINFO* this_ptr, void* not_used) {
	return false; // Allows any race/illusion to ride
}

typedef int(__thiscall* EQ_FUNCTION_TYPE_EQPlayer__IsUntexturedHorse)(void* this_ptr);
EQ_FUNCTION_TYPE_EQPlayer__IsUntexturedHorse IsUntexturedHorse_Trampoline;
int __fastcall IsUntexturedHorse_Detour(EQSPAWNINFO* horse, void* not_used)
{
	bool faked = FakeHorseRace(horse);
	int result = IsUntexturedHorse_Trampoline(horse);
	UnFakeHorseRace(horse, faked);
	return result;
}

typedef void(__thiscall* EQ_FUNCTION_TYPE_EQPlayer__MountEQPlayer)(EQSPAWNINFO* this_ptr, EQSPAWNINFO* mount);
EQ_FUNCTION_TYPE_EQPlayer__MountEQPlayer EQPlayer__MountEQPlayer_Trampoline;
void __fastcall EQPlayer__MountEQPlayer_Detour(EQSPAWNINFO* this_ptr, int unused, EQSPAWNINFO* horse)
{
	bool faked = FakeHorseRace(horse);

	BYTE* cdisplay = *(BYTE**)EQ_POINTER_CDisplay;
	BYTE display_0xA0 = cdisplay[0xA0];

#ifdef HORSE_LOGGING
	print_chat("MountEQPlayer: horse = %08x, cur_horse_race = %u (custom: %u), Display[0xA0]=%u", (uintptr_t)horse, horse ? horse->Race : 0, ActualHorseRaceID, display_0xA0);
#endif

	cdisplay[0xA0] = 1;
	EQPlayer__MountEQPlayer_Trampoline(this_ptr, horse);
	cdisplay[0xA0] = display_0xA0;

	UnFakeHorseRace(horse, faked);
}

typedef void(__thiscall* EQ_FUNCTION_TYPE_CEverquest__ProcessControls)(void* this_ptr);
EQ_FUNCTION_TYPE_CEverquest__ProcessControls CEverquest__ProcessControls_Trampoline;
void __fastcall CEverquest__ProcessControls_Detour(void* this_ptr, int unused)
{
	EQSPAWNINFO* controlled = EQ_OBJECT_ControlledSpawn;
	bool faked = controlled && controlled->ActorInfo && controlled->ActorInfo->Rider && FakeHorseRace(controlled);
	CEverquest__ProcessControls_Trampoline(this_ptr);
	UnFakeHorseRace(controlled, faked);
}

typedef int(__stdcall* EQ_FUNCTION_TYPE_EQPlayer__AttachPlayerToDag)(EQSPAWNINFO* player, EQSPAWNINFO* horse, EQDAGINFO* use_dag);
EQ_FUNCTION_TYPE_EQPlayer__AttachPlayerToDag EQPlayer__AttachPlayerToDag_Trampoline;
int __stdcall EQPlayer__AttachPlayerToDag_Detour(EQSPAWNINFO* player, EQSPAWNINFO* horse, EQDAGINFO* use_dag)
{
	bool faked = FakeHorseRace(horse);
	int result = EQPlayer__AttachPlayerToDag_Trampoline(player, horse, use_dag);
#ifdef HORSE_LOGGING
	print_chat("AttachPlayerToDag: returned %i use_dag was %08x %s", result, (uintptr_t)use_dag, use_dag ? use_dag->Name : "");
#endif
	UnFakeHorseRace(horse, faked);
	return result;
}

typedef void(__thiscall* EQ_FUNCTION_TYPE_EQPlayer__Dismount)(EQSPAWNINFO* this_ptr);
EQ_FUNCTION_TYPE_EQPlayer__Dismount EQPlayer__Dismount_Trampoline;
void __fastcall EQPlayer__Dismount_Detour(EQSPAWNINFO* player, int unused)
{
	if (!player || !player->ActorInfo || !player->ActorInfo->Mount)
	{
		EQPlayer__Dismount_Trampoline(player);
		return;
	}
	
	bool faked = FakeHorseRace(player->ActorInfo->Mount);
	EQPlayer__Dismount_Trampoline(player);
	UnFakeHorseRace(player->ActorInfo->Mount, faked);
}

// --------------------------------------------------------------------------
// Legacy Model Horse Support [End]
// --------------------------------------------------------------------------

// --------------------------------------------------------------------------
// Mesmerization Fix
// --------------------------------------------------------------------------

// Modified Version of EQCharacter::StunMe(duration) that overrides their current stun even if they are already stunned.
// This needs to happen for mez effects to be able to extend themselves or apply while the player is already stunned.
__int16 __fastcall EQCharacter__ForceStunMe(EQCHARINFO* charinfo, int unused, unsigned int duration)
{
	EQSPAWNINFO* entity = charinfo->SpawnInfo;
	if (entity)
	{
		EQACTORINFO* actor_info = entity->ActorInfo;
		if (actor_info)
		{
			short divine_aura = EQ_Character::TotalSpellAffects(charinfo, 40, 1, 0);// SE_DivineAura
			if (divine_aura <= 0)
			{
				unsigned int dur = duration;
				if (duration < 1000)
				{
					entity = charinfo->SpawnInfo;
					if (!entity || entity->Type)
						return (__int16)entity;
					dur = 1000;
				}
				__int64 end_time = dur + EqGetTime();
				if (actor_info->StunnedUntilTime < end_time)
				{
					actor_info->StunnedUntilTime = end_time;
					charinfo->StunnedState = 1;
					CDisplay::SetSpecialEnvironment(23);
					entity->MovementSpeed = 0.0;
					if (actor_info->Mount)
						actor_info->Mount->MovementSpeed = 0.0;
					char* string_12479 = EQ_CLASS_StringTable->getString(12479, 0);
					EQ_CLASS_CEverQuest->dsp_chat(string_12479, 273, true);
				}
			}
		}
	}
	return (__int16)entity;
}

void ApplyMesmerizationFixes()
{
	// HitBySpell -> SE_Mez -> ForceStunMe()
	PatchCall(0x4CA352, (uintptr_t)EQCharacter__ForceStunMe); // Replace call to EQCharacter::StunMe()
}

// --------------------------------------------------------------------------
// Mesmerization Fix [end]
// --------------------------------------------------------------------------

#define EQZoneInfo_AddZoneInfo 0x00523AEB
#define EQZoneInfo_AddZoneInfo 0x00523AEB

// Define a structure to store a row of CSV data
struct CSVRow {
	std::vector<std::string> columns;
};

// Utility function to parse a CSV file and key rows by index
std::vector<CSVRow> parseCSVWithIndex(const std::string& filePath) {
	std::vector<CSVRow> data;
	std::ifstream file(filePath);

	if (!file.is_open()) {
		return data;
	}

	std::string line;
	while (std::getline(file, line)) {
		CSVRow row;
		std::stringstream lineStream(line);
		std::string cell;

		while (std::getline(lineStream, cell, '^')) {
			row.columns.push_back(cell);
		}

		data.push_back(row);
	}

	file.close();
	return data;
}



typedef int(__thiscall* EQ_FUNCTION_TYPE_EQZoneInfo__EQZoneInfo)(void* this_ptr);
EQ_FUNCTION_TYPE_EQZoneInfo__EQZoneInfo EQZoneInfo_Ctor_Trampoline;
int __fastcall EQZoneInfo_Ctor_Detour(void* this_ptr, void* not_used) {
	int ctor_result = EQZoneInfo_Ctor_Trampoline(this_ptr);

	auto data = parseCSVWithIndex("ZoneData.txt");

	if (data.size())
	{
		for (auto& entry : data)
		{
			std::vector<std::string>& column = entry.columns;
			if (column.size() == 7)
			{
				if (column[0].empty())
					continue;
				else if (column[1].empty())
					continue;
				else if (column[2].empty())
					continue;
				else if (column[3].empty())
					continue;
				else if (column[4].empty())
					continue;
				else if (column[5].empty())
					continue;
				else if (column[6].empty())
					continue;

				unsigned int zoneIdNum = std::atoi(column[0].c_str());
				const char* zoneShortName = column[1].c_str();
				const char* zoneLongName = column[2].c_str();
				unsigned int zoneUnk = std::atoi(column[3].c_str());
				unsigned int zoneUnk2 = std::atoi(column[4].c_str());
				unsigned int zoneUnk3 = std::atoi(column[5].c_str());
				unsigned int zoneUnk4 = std::atoi(column[6].c_str());

				((int(__thiscall*) (LPVOID, int, int, const char*, const char*, int, unsigned long, int, int)) EQZoneInfo_AddZoneInfo) (this_ptr, 0, zoneIdNum, zoneShortName, zoneLongName, zoneUnk, zoneUnk2, zoneUnk3, zoneUnk4);
			}
		}
	}

	/*((int(__thiscall*) (LPVOID, int, int, const char*, const char*, int, unsigned long, int, int)) EQZoneInfo_AddZoneInfo) (this_ptr, 0, 224, "gunthak", "Gulf of Gunthak", 4048, 4, 0, 0);
	((int(__thiscall*) (LPVOID, int, int, const char*, const char*, int, unsigned long, int, int)) EQZoneInfo_AddZoneInfo) (this_ptr, 0, 225, "dulak", "Dulak's Harbor", 4049, 4, 0, 0);
	((int(__thiscall*) (LPVOID, int, int, const char*, const char*, int, unsigned long, int, int)) EQZoneInfo_AddZoneInfo) (this_ptr, 0, 229, "guka", "The Citadel of Guk", 2247, 7, 0, 0);*/

	return ctor_result;
}


// Function to read a CSV file and store the data in a vector of pairs
std::vector<std::pair<std::string, std::string>> readChrTextFile(const std::string& filePath) {
	std::vector<std::pair<std::string, std::string>> data;
	std::ifstream inputFile = std::ifstream(filePath);

	if (!inputFile.is_open()) {
		std::cerr << "Error: Could not open file " << filePath << std::endl;
		return data;
	}

	std::string line;
	// Skip the first line containing the number of entries
	if (std::getline(inputFile, line)) {
		// First line read but not processed
	}

	// Read the remaining lines
	while (std::getline(inputFile, line)) {
		std::istringstream lineStream(line);
		std::string first, second;

		if (std::getline(lineStream, first, ',') && std::getline(lineStream, second)) {
			data.emplace_back(first, second);
		}
		else {
			std::cerr << "Error: Malformed line \"" << line << "\"" << std::endl;
		}
	}

	inputFile.close();
	return data;
}

//typedef int(__thiscall* EQ_FUNCTION_TYPE_CDisplay_InitWorld)(void* this_ptr);
//EQ_FUNCTION_TYPE_CDisplay_InitWorld EQZoneInfo_CDisplay_InitWorld;
//int __fastcall EQZoneInfo_CDisplay_InitWorld(void* this_ptr, void* not_used, char* a2, char* a3, int a4, int a5, int a6) {
//	if (a4 == 1 && a2)
//	{
//		std::string zoneName = a2;
//		zoneName += ".chr.txt";
//		auto data = readChrTextFile(a2);
//		for (auto& pair : data)
//		{
//			((int(__thiscall*) (LPVOID, a2, a3, int, int, int)) 0x004A7D62) (this_ptr, pair.second.c_str(), pair.second.c_str()))
//		}
//	}
//}

struct RaceData {
	BYTE gender = 0;
	std::string code;
};

std::map<unsigned int, RaceData> raceIdToCodeMap;

typedef int(__thiscall* EQ_FUNCTION_TYPE_EQPlayer_GetActorTag)(EQSPAWNINFO* this_ptr, char* a2);
EQ_FUNCTION_TYPE_EQPlayer_GetActorTag EQPlayer_GetActorTag_Trampoline;
int __fastcall EQPlayer_GetActorTag_Detour(EQSPAWNINFO* this_ptr, void* not_used, char* a2) {

	WORD ourRace = this_ptr->Race;
	BYTE ourGender = this_ptr->Gender;

	// Temporarily restore the actual horse race when GetActorTag runs
	if (this_ptr->Race == 216)
		this_ptr->Race = GetActualHorseRaceID(this_ptr);

	int res = EQPlayer_GetActorTag_Trampoline(this_ptr, a2);

	// Restore the horse to race 216
	this_ptr->Race = ourRace;	

	std::map<unsigned int, RaceData>::iterator it = raceIdToCodeMap.find(ourRace);
	if (it != raceIdToCodeMap.end())
	{
		if (it->second.gender == ourGender)
		{
			strcpy(a2, it->second.code.c_str());
		}
	}
	return res;
}

int __cdecl CityCanStart_Detour(int a1, int a2, int a3, int a4) {
	return CityCanStart_Trampoline(a1, a2, a3, a4);
}

int __cdecl ProcessKeyUp_Detour(int a1)
{
#ifdef LOGGING
	std::string outstring;
	outstring = "EQGAME: KeyPress Up = ";
	outstring += std::to_string(a1);
	WriteLog(outstring);
#endif
	if (!has_focus || has_focus && ((GetTickCount() - focus_regained_time) <= 10))
		return ProcessKeyUp_Trampoline(0x00);

	return ProcessKeyUp_Trampoline(a1);
}

int __cdecl ProcessKeyDown_Detour(int a1)
{
#ifdef LOGGING
	std::string outstring;
	outstring = "EQGAME: KeyPress Down = ";
	outstring += std::to_string(a1);
	WriteLog(outstring);
#endif

	if (!has_focus || has_focus && ((GetTickCount() - focus_regained_time) <= 10))
		return ProcessKeyDown_Trampoline(0x00);

	SetEQhWnd();
	if (EQ_OBJECT_CEverQuest != NULL && can_fullscreen && EQ_OBJECT_CEverQuest->GameState > 0 && a1 == 0x1c && AltPressed() && !ShiftPressed() && !CtrlPressed()) {
#ifdef LOGGING
		WriteLog("EQGAME: Alt - Enter Detected");
#endif
		//MessageBox(NULL, "Alt-Enter Detected", NULL, MB_OK);
		if (bWindowedMode) {
#ifdef LOGGING
			WriteLog("EQGAME: Currently in windowed mode.");
#endif
			ResetMouseFlags();

			// store window positions
			if (!window_info_stored) {
				GetWindowInfo(EQhWnd, &stored_window_info);
				window_info_stored = true;
			}

			// removed borders, etc.
			SetWindowLong(EQhWnd, GWL_STYLE,
				stored_window_info.dwStyle & ~(WS_CAPTION | WS_THICKFRAME | WS_SYSMENU));

			SetWindowLong(EQhWnd, GWL_EXSTYLE,
				stored_window_info.dwExStyle & ~(WS_EX_DLGMODALFRAME |
					WS_EX_WINDOWEDGE | WS_EX_CLIENTEDGE | WS_EX_STATICEDGE));

			// find points to use for current monitor
			MONITORINFO monitor_info;
			monitor_info.cbSize = sizeof(monitor_info);
			GetMonitorInfo(MonitorFromWindow(EQhWnd, MONITOR_DEFAULTTONEAREST),
				&monitor_info);
			RECT window_rect(monitor_info.rcMonitor);

			WINDOWPLACEMENT window_placement;
			window_placement.length = sizeof(window_placement);

			if (first_maximize) {
				GetWindowPlacement(EQhWnd, &window_placement);
				window_placement.showCmd = SW_MINIMIZE;
				SetWindowPlacement(EQhWnd, &window_placement);
				window_placement.showCmd = SW_MAXIMIZE;
				SetWindowPlacement(EQhWnd, &window_placement);
			}
			SetWindowPos(EQhWnd, HWND_TOP, window_rect.left, window_rect.top,
				window_rect.right - window_rect.left, window_rect.bottom - window_rect.top,
				SWP_NOOWNERZORDER | SWP_FRAMECHANGED | SWP_NOSENDCHANGING | SWP_SHOWWINDOW);

			char szDefault[255];

			sprintf(szDefault, "%s", "FALSE");
			WritePrivateProfileStringA_tramp("Options", "WindowedMode", szDefault, "./eqclient.ini");
			start_fullscreen = true;
			first_maximize = false;
		}
		else
		{
			//ResetMouseFlags();
#ifdef LOGGING
			WriteLog("EQGAME: Currently in full screen mode.");
#endif
			SetWindowLong(EQhWnd, GWL_STYLE, stored_window_info.dwStyle | WS_CAPTION );
			SetWindowLong(EQhWnd, GWL_EXSTYLE, stored_window_info.dwExStyle);
			if (window_info_stored) {
				SetWindowPos(EQhWnd, HWND_TOP, stored_window_info.rcWindow.left, stored_window_info.rcWindow.top,
					stored_window_info.rcWindow.right - stored_window_info.rcWindow.left, stored_window_info.rcWindow.bottom - stored_window_info.rcWindow.top,
					SWP_NOOWNERZORDER | SWP_FRAMECHANGED | SWP_NOSENDCHANGING | SWP_SHOWWINDOW);
			}
			char szDefault[255];
			sprintf(szDefault, "%s", "TRUE");
			WritePrivateProfileStringA_tramp("Options", "WindowedMode", szDefault, "./eqclient.ini");
			start_fullscreen = false;
		}
		bWindowedMode = !bWindowedMode;
		return ProcessKeyDown_Trampoline(0x00); // null
	}

	return ProcessKeyDown_Trampoline(a1);
}

DWORD WINAPI GetModuleFileNameA_detour(HMODULE hMod,LPTSTR outstring,DWORD nSize)
{
	DWORD allocsize = nSize;
	DWORD ret = GetModuleFileNameA_tramp(hMod,outstring,nSize);
	if(bExeChecksumrequested) {
		if(hMod == nullptr)
		{
			bExeChecksumrequested=0;
			PCHAR szProcessName = 0;
			szProcessName = strrchr(outstring,'\\');
			szProcessName[0] = '\0';
			sprintf_s(outstring,allocsize,"%s\\eqgame.dll",outstring);
		}
	}
	return ret;
}

int new_height;
int new_width;

DWORD WINAPI WritePrivateProfileStringA_detour(LPCSTR lpAppName, LPCSTR lpKeyName, LPCSTR lpString, LPCSTR lpFileName)
{
	if (lstrcmp(lpAppName, "Positions") == 0) {
		// if in fullscreen mode, we do not want to write out positions to eqw.ini
		// switching from char select can reset also
		if (EQ_OBJECT_CEverQuest != NULL && EQ_OBJECT_CEverQuest->GameState != 5 && lstrcmp(lpString, "0") == 0) {
			return true;
		}
		if (!bWindowedMode)
			return true;
	}
	DWORD ret = WritePrivateProfileStringA_tramp(lpAppName, lpKeyName, lpString, lpFileName);
	
	if (lstrcmp(lpAppName, "VideoMode") == 0) {
		if (lstrcmp(lpKeyName, "Height") == 0) {
			if (!bWindowedMode)
				window_info_stored = false;
			new_height = atoi(lpString);
		} else if (lstrcmp(lpKeyName, "Width") == 0) {
			if (!bWindowedMode)
				window_info_stored = false;
			new_width = atoi(lpString);
		}
		else if (lstrcmp(lpKeyName, "BitsPerPixel") == 0) {

			if (resy != new_height || resx != new_width) {
				ResolutionStored = false;
				resx = new_width;
				resy = new_height;

				if (!bWindowedMode) {
					// go out of full screen
					SetEQhWnd();
					SetWindowLong(EQhWnd, GWL_STYLE, stored_window_info.dwStyle | WS_CAPTION );
					SetWindowLong(EQhWnd, GWL_EXSTYLE, stored_window_info.dwExStyle);
					
					// eqw will adjust window to default loc for this resolution
					// store the windowed location
					GetWindowInfo(EQhWnd, &stored_window_info);
					window_info_stored = true;


					// removed borders, etc.
					SetWindowLong(EQhWnd, GWL_STYLE,
						stored_window_info.dwStyle & ~(WS_CAPTION | WS_THICKFRAME | WS_SYSMENU));

					SetWindowLong(EQhWnd, GWL_EXSTYLE,
						stored_window_info.dwExStyle & ~(WS_EX_DLGMODALFRAME |
							WS_EX_WINDOWEDGE | WS_EX_CLIENTEDGE | WS_EX_STATICEDGE));

					// restore back to full screen
					MONITORINFO monitor_info;
					monitor_info.cbSize = sizeof(monitor_info);
					GetMonitorInfo(MonitorFromWindow(EQhWnd, MONITOR_DEFAULTTONEAREST),
						&monitor_info);
					RECT window_rect(monitor_info.rcMonitor);

					WINDOWPLACEMENT window_placement;
					window_placement.length = sizeof(window_placement);

					SetWindowPos(EQhWnd, HWND_TOP, window_rect.left, window_rect.top,
						window_rect.right - window_rect.left, window_rect.bottom - window_rect.top,
						SWP_NOOWNERZORDER | SWP_FRAMECHANGED | SWP_NOSENDCHANGING | SWP_SHOWWINDOW);

				} else {
					// we need to save the new windowed mode position
					GetWindowInfo(EQhWnd, &stored_window_info);
					first_maximize = true;
				}
			}
		}
	}

	return ret;
}


const bool IsMouseOverWindow(HWND hWnd, const int mx, const int my,
	const bool inClientSpace /*= false */)
{
	if (!IsWindowVisible(hWnd))
		return false;

	RECT windowRect;

	// Get the window in screen space
	::GetWindowRect(hWnd, &windowRect);

	if (inClientSpace)
	{
		POINT offset;
		offset.x = offset.y = 0;
		ClientToScreen(hWnd, &offset);

		// Offset the window to client space
		windowRect.left -= offset.x;
		windowRect.top -= offset.y;
		// NOTE: left and top should now be 0, 0
		windowRect.right -= offset.x;
		windowRect.bottom -= offset.y;
	}

	// Test if mouse over window
	POINT cursorPos = { mx, my };
	return PtInRect(&windowRect, cursorPos);
}

signed int __cdecl ProcessMouseEvent_Hook()
{
	bool shouldRetEarly = false;
	signed int ret = 0;

	SetEQhWnd();

#ifdef FREE_THE_MOUSE
	POINT p;
	GetCursorPos(&p);
	BYTE dval = *(BYTE*)0x007985EA;

	if (dval == 0) {
		if (!IsMouseOverWindow(EQhWnd, p.x, p.y, false))
		{
			EQ_flush_mouse();
			EQ_SetMousePosition(32767, 32767);
			while (ShowCursor(FALSE) >= 0);
			if (posPoint.x == 0 && posPoint.y == 0)
			{
				return ret;
			}
		}
		// we have stored cursor positions
		// restore cursor to previous position
		if (posPoint.x != 0 && posPoint.y != 0 && (GetForegroundWindow() == EQhWnd))
		{
			POINT pt;
			pt.x = posPoint.x;
			pt.y = posPoint.y;
			ClientToScreen(EQhWnd, &pt);
			SetCursorPos(pt.x, pt.y);
			EQ_SetMousePosition(posPoint.x, posPoint.y);
			posPoint.x = 0;
			posPoint.y = 0;
			shouldRetEarly = true;
			while (ShowCursor(TRUE) < 0);
		}
	}
#endif

	ret = return_ProcessMouseEvent();

	if (!RightHandMouse) {
		*(BYTE*)0x00798616 = BYTE1(*(DWORD*)0x8090B4) != 0;
		*(BYTE*)0x00798617 = BYTE2(*(DWORD*)0x8090B4) != 0;
	}


	if (mouse_looking && (GetForegroundWindow() == EQhWnd))
	{
		if (savedRMousePos.x != 0 && savedRMousePos.y != 0)
		{
			POINT pt;
			pt.x = savedRMousePos.x;
			pt.y = savedRMousePos.y;
			ClientToScreen(EQhWnd, &pt);
			SetCursorPos(pt.x, pt.y);
			EQ_SetMousePosition(savedRMousePos.x, savedRMousePos.y);
		}
	}
	else if (!mouse_looking || (GetForegroundWindow() != EQhWnd))
	{
		savedRMousePos.x = 0;
		savedRMousePos.y = 0;
	}

#ifdef FREE_THE_MOUSE
	if (shouldRetEarly)
	{
		return ret;
	}
	if (EQhWnd)
	{
		if (ScreenToClient(EQhWnd, &p))
		{
			if (dval == 0)
			{
				*(DWORD*)0x008092E8 = p.x;
				*(DWORD*)0x008092EC = p.y;
			}
			else
			{
				if (posPoint.x == 0 && posPoint.y == 0)
				{
					posPoint.x = *(DWORD*)0x008092E8;
					posPoint.y = *(DWORD*)0x008092EC;
					while (ShowCursor(FALSE) >= 0);
				}
			}
		}
	}
#endif
	return ret;
}

void InitRaceShortCodeMap()
{
	raceIdToCodeMap.clear();
	auto parsedMap = parseCSVWithIndex("RaceData.txt");
	if (parsedMap.size())
	{
		for (auto& entry : parsedMap)
		{
			std::vector<std::string>& column = entry.columns;
			if (column.size() == 3)
			{
				if (column[0].empty())
					continue;
				else if (column[1].empty())
					continue;
				else if (column[2].empty())
					continue;

				unsigned int raceIdNum = std::atoi(column[0].c_str());
				unsigned int genderIdNum = std::atoi(column[1].c_str());
				std::string raceCodeId = column[2];

				RaceData rData;
				rData.gender = genderIdNum;
				rData.code = raceCodeId;

				raceIdToCodeMap.emplace(raceIdNum, rData);
			}
		}
	}
}

/*signed int __cdecl SetMouseCenter_Hook()//55B722
{
	signed int retval = return_SetMouseCenter();
	if (EQhWnd)
	{
		RECT windowRect;
		::GetWindowRect(EQhWnd, &windowRect);
		int width = windowRect.right - windowRect.left;
		int height = windowRect.bottom - windowRect.top;
		POINT pt;
		pt.x = posPoint.x;
		pt.y = posPoint.y;
		ClientToScreen(EQhWnd, &pt);
		SetCursorPos(pt.x, pt.y);

	}
	return retval;
}*/
extern void LoadIniSettings();

int __fastcall EQMACMQ_DETOUR_CEverQuest__InterpretCmd(void* this_ptr, void* not_used, class EQPlayer* a1, char* a2)
{
	if (a1 == NULL || a2 == NULL)
	{
		return EQMACMQ_REAL_CEverQuest__InterpretCmd(this_ptr, a1, a2);
	}

	if (strlen(a2) == 0)
	{
		return EQMACMQ_REAL_CEverQuest__InterpretCmd(this_ptr, NULL, NULL);
	}

	// double slashes not needed, convert "//" to "/" by removing first character
	if (strncmp(a2, "//", 2) == 0)
	{
		memmove(a2, a2 + 1, strlen(a2));
	}
	if (strcmp(a2, "/fps") == 0) {
		// enable fps indicator
		if (eqgfxMod) {
			if (*(BYTE*)(eqgfxMod + 0x00A4F770) == 0)
				*(BYTE*)(eqgfxMod + 0x00A4F770) = 1;
			else
				*(BYTE*)(eqgfxMod + 0x00A4F770) = 0;
		}
		return EQMACMQ_REAL_CEverQuest__InterpretCmd(this_ptr, NULL, NULL);
	}

	if (strcmp(a2, "/rfps") == 0) {
		LoadIniSettings();

		return EQMACMQ_REAL_CEverQuest__InterpretCmd(this_ptr, NULL, NULL);
	}

	if (strcmp(a2, "/rnpcdata") == 0) {
		InitRaceShortCodeMap();
		return EQMACMQ_REAL_CEverQuest__InterpretCmd(this_ptr, NULL, NULL);
	}

	if (strcmp(a2, "/songs") == 0) {
		g_bSongWindowAutoHide = !g_bSongWindowAutoHide;
		WritePrivateProfileStringA_tramp("Defaults", "SongWindowAutoHide", g_bSongWindowAutoHide ? "TRUE" : "FALSE", "./eqclient.ini");
		print_chat("Song Window auto-hide: %s.", g_bSongWindowAutoHide ? "ON" : "OFF");
		if (!g_bSongWindowAutoHide && GetShortDurationBuffWindow() && !GetShortDurationBuffWindow()->IsVisibile()) {
			GetShortDurationBuffWindow()->Show(1, 1);
		}
		return 0;
	}

	else if ((strcmp(a2, "/raiddump") == 0) || (strcmp(a2, "/outputfile raid") == 0)) {
		// beginning of raid structure
		DWORD raid_ptr = 0x007914D0;
		DWORD name_ptr = raid_ptr + 72;
		DWORD level_ptr = raid_ptr + 136;
		DWORD class_ptr = raid_ptr + 144;
		DWORD is_leader_ptr = raid_ptr + 275;
		DWORD group_num_ptr = raid_ptr + 276;

		CHAR RaidLeader[64];
		CHAR CharName[64];
		CHAR Class[64];
		CHAR Level[8];
		int i = 0;
		if (*(BYTE*)(raid_ptr) == 1) {
			memcpy(RaidLeader, (char *)(0x794FA0), 64);
			char v50[64];
			char v51[256];
			time_t a2;
			a2 = time(0);
			struct tm * v4;
			v4 = localtime(&a2);
			sprintf(
				v50,
				"%04d%02d%02d-%02d%02d%02d",
				v4->tm_year + 1900,
				v4->tm_mon + 1,
				v4->tm_mday,
				v4->tm_hour,
				v4->tm_min,
				v4->tm_sec);
			sprintf(v51, "RaidRoster-%s.txt", v50);
			FILE *result;
			result = fopen(v51, "w");
			if (result != NULL) {

				while (*(BYTE *)(raid_ptr) == 1) {
					memcpy(CharName, (char *)(name_ptr), 64);
					memcpy(Level, (char *)(level_ptr), 8);
					memcpy(Class, (char *)(class_ptr), 64);
					bool group_leader = (bool)*(CHAR *)(is_leader_ptr);
					int group_num = (int)*(CHAR *)(group_num_ptr);
					group_num++;
					std::string type = "";
					if (group_leader)
						type = "Group Leader";
					if (strcmp(CharName, RaidLeader) == 0)
						type = "Raid Leader";
					raid_ptr++;
					name_ptr += 208;
					level_ptr += 208;
					class_ptr += 208;
					is_leader_ptr += 208;
					group_num_ptr += 208;

					fprintf(result, "%d\t%s\t%s\t%s\t%s\t%s\n", group_num, CharName, Level, Class, type.c_str(), "");
				}
				fclose(result);
			}
		}
		return EQMACMQ_REAL_CEverQuest__InterpretCmd(this_ptr, NULL, NULL);
	}

	return EQMACMQ_REAL_CEverQuest__InterpretCmd(this_ptr, a1, a2);
}


int __cdecl SendExeChecksum_Detour()
{
	bExeChecksumrequested = 1;
	return SendExeChecksum_Trampoline();
}

int sprintf_Detour_loadskin(char *const Buffer, const char *const format, ...)
{
	va_list ap;

	va_start(ap, format);
	char *cxstr = va_arg(ap, char *);
	cxstr += 20; // get the buffer inside the CXStr
	char useini = va_arg(ap, char);
	va_end(ap);

	return sprintf(Buffer, format, cxstr, useini);
}

void SendDllVersion_OnZone()
{
	SendCustomSpawnAppearanceMessage(DLL_VERSION_MESSAGE_ID, DLL_VERSION, true);
}

// Re-sends the DllVersion if the server requested it from us
bool HandleDllVersionRequest(DWORD id, DWORD value, bool is_request)
{
	if (id == DLL_VERSION_MESSAGE_ID)
	{
		if (is_request)
		{
			SendCustomSpawnAppearanceMessage(DLL_VERSION_MESSAGE_ID, DLL_VERSION, false);
		}
		return true;
	}
	return false;
}

// ---------------------------------------------------------------------------------
// BuffStacking Patches
// ---------------------------------------------------------------------------------
// - Makes Bard Selo's line stack with normal movement spells (Accel/Travel/Chorus).
// - Makes normal buffs able to land without having to temporarily pause bard songs. This was a client bug, because the reverse was already allowed (bard songs could land/stack with normal buffs).
// - Fixes broken checking that checked whether the target/caster was a bard, rather than just the spell being a bard song. Now we just care whether it's a bardsong.
//----------------------------------------------------------------------------------

// Handshake "opcodes" sent to OP_SpawnAppearance (these values must be implemented on the server)
constexpr WORD CustomSpawnAppearanceMessage_BuffStackingPatchWithSongWindowHandshake = 2;
constexpr WORD CustomSpawnAppearanceMessage_BuffStackingPatchWithoutSongWindowHandshake = 3;
constexpr WORD BSP_VERSION_1 = 1; // Buff Stacking feature flag sent to the server in the handshake

// Short Buff Window
CShortBuffWindow* ShortBuffWindow = nullptr;
// Set during ShortBuffWindow's refresh logic, so it reads from offset 15 (because it shares logic with CBuffWindow)
thread_local bool ShortBuffSupport_ReturnSongBuffs = false;

// -- [Handshake / Initialization] --

void BuffstackingPatch_OnZone()
{
	// Send handshake message to enable the client/server buffstacking changes.
	bool is_new_ui = *(BYTE*)0x8092D8 != 0;
	if (is_new_ui)
		SendCustomSpawnAppearanceMessage(CustomSpawnAppearanceMessage_BuffStackingPatchWithSongWindowHandshake, BSP_VERSION_1, true);
	else
		SendCustomSpawnAppearanceMessage(CustomSpawnAppearanceMessage_BuffStackingPatchWithoutSongWindowHandshake, BSP_VERSION_1, true);
}

// Callback notification on server response to handshake
bool BuffstackingPatch_HandleHandshake(DWORD id, DWORD value, bool is_request)
{

	bool send_response = is_request;
	bool enabled = false;
	int enabled_songs = 0;

	if (id == CustomSpawnAppearanceMessage_BuffStackingPatchWithSongWindowHandshake)
	{
		if (value == BSP_VERSION_1)
		{
			enabled = true;
			enabled_songs = 6;
		}
		else
		{
			value = 0;
		}
	}
	else if (id == CustomSpawnAppearanceMessage_BuffStackingPatchWithoutSongWindowHandshake)
	{
		if (value == BSP_VERSION_1)
		{
			enabled = true;
			enabled_songs = 0;
		}
		else
		{
			value = 0;
		}
	}
	else
	{
		return false;
	}

	// Handshake Complete.
	Rule_Buffstacking_Patch_Enabled = enabled;
	Rule_Max_Buffs = EQ_NUM_BUFFS + enabled_songs;
	Rule_Num_Short_Buffs = enabled_songs;
	if (send_response)
	{
		SendCustomSpawnAppearanceMessage(id, value, false);
	}
	return true;
}

// -- [Helper Functions] --

// This helps us iterate in the right buff order when the song window is involved.
// Song window starts at logical buff offset 15, then loop back around to offset 0 after if no song slots are open.
inline int BSP_ToBuffSlot(int i, int start_offset, int modulo) {
	return (i + start_offset) % modulo;
}
// Fixed bug -- The old logic checked if the spell target was also a bard (obvious bug), rather than just spell's class.
bool BSP_IsStackBlocked(EQCHARINFO* player, _EQSPELLINFO* spell) {
	return (spell && spell->IsBardsong()) 
		? false
		: EQ_Character::IsStackBlocked(player, spell);
}
// Allows selos to stack with regular movement effects.
int BSP_SpellAffectIndex(_EQSPELLINFO* spell, int effectType)
{
	return (effectType == SE_MovementSpeed && spell->IsBeneficial() && spell->IsBardsong())
		? 0
		: EQ_Spell::SpellAffectIndex(spell, effectType);
}

// -- [Main Patch] --
// - This function replaces the client's buffstacking logic.
// - This is faithful to original implementation (and the server), but has our new bug fixes/modifications for stacking, and support for the song window.
// - All changes here need to be mirrored on the server.
_EQBUFFINFO* BSP_FindAffectSlot(EQCHARINFO* player, WORD spellid, _EQSPAWNINFO* caster, DWORD* result_buffslot, int dry_run)
{
	*result_buffslot = -1;
	if (!caster || !EQ_Spell::IsValidSpellIndex(spellid))
		return 0;

	EQSPELLINFO* new_spell = EQ_Spell::GetSpell(spellid);
	if (!new_spell || !caster->Type && BSP_IsStackBlocked(player, new_spell)) // [Patch:Main] See: IsStackBlocked
		return 0;

	int MaxTotalBuffs = Rule_Max_Buffs;
	int StartBuffOffset = 0;
	int MaxSelectableBuffs = EQ_NUM_BUFFS;

	// [Patch:SongWindow] If song window is enabled, songs can search those first
	if (Rule_Num_Short_Buffs > 0 && EQ_Spell::IsShortBuffBox(spellid)) {
		// Song: Start in slots 16+, then wrap around to 1-15 if no slot open.
		StartBuffOffset = EQ_NUM_BUFFS;
		// Song: Allow using all buff slots
		MaxSelectableBuffs = MaxTotalBuffs;
	}

	WORD old_buff_spell_id = 0;
	EQBUFFINFO* old_buff = 0;
	EQSPELLINFO* old_spelldata = 0;
	int cur_slotnum7 = 0;
	int cur_slotnum7_buffslot = BSP_ToBuffSlot(cur_slotnum7, StartBuffOffset, MaxSelectableBuffs);
	BYTE new_buff_effect_id2 = 0;
	int effect_slot_num = 0;
	bool no_slot_found_yet = true;
	bool old_effect_is_negative_or_zero = false;
	bool old_effect_value_is_negative_or_zero = false;
	bool is_bard_song = new_spell->IsBardsong();
	bool is_movement_effect = BSP_SpellAffectIndex(new_spell, SE_MovementSpeed) != 0; // [Patch:Main] Optimization - Caching the value.
	short old_effect_value;
	short new_effect_value;

	if (is_bard_song) // [Patch:Main] - Removed: caster->Class == BARD
	{
		for (int i = 0; i < MaxTotalBuffs; i++)
		{
			int buffslot = i; // This first loop is just checking for basic blocking, we can skip the buff/offset translation check
			EQBUFFINFO* buff = EQ_Character::GetBuff(player, buffslot);
			if (buff->BuffType)
			{
				WORD buff_spell_id = buff->SpellId;
				if (EQ_Spell::IsValidSpellIndex(buff_spell_id))
				{
					EQSPELLINFO* buff_spell = EQ_Spell::GetSpell(buff_spell_id);
					if (buff_spell
						&& !buff_spell->IsBardsong()
						&& !buff_spell->IsBeneficial()
						&& new_spell->IsBeneficial()
						&& is_movement_effect
						&& (BSP_SpellAffectIndex(buff_spell, SE_MovementSpeed) != 0 || BSP_SpellAffectIndex(buff_spell, SE_Root) != 0))
					{
						*result_buffslot = -1;
						return 0;
					}
				}
			}
		}
	}

	bool can_multi_stack = EQ_Spell::CanSpellStackMultipleTimes(new_spell);
	bool spell_id_already_affecting_target = false;

	for (int i = 0; i < MaxSelectableBuffs; i++) {
		int buffslot = BSP_ToBuffSlot(i, StartBuffOffset, MaxSelectableBuffs); // [Patch:SongWindow] Translates the 'i' value to the right buffslot order.
		EQBUFFINFO* buff = EQ_Character::GetBuff(player, buffslot);
		if (buff->BuffType)
		{
			WORD buff_spell_id = buff->SpellId;
			if (buff_spell_id == spellid)
			{
				EQSPAWNINFO* SpawnInfo = player->SpawnInfo;
				if (!SpawnInfo || caster->Type != EQ_SPAWN_TYPE_PLAYER || SpawnInfo->Type != EQ_SPAWN_TYPE_NPC)
					goto OVERWRITE_SAME_SPELL_WITHOUT_REMOVING_FIRST;
				if (buff_spell_id == 2755) // Lifeburn
					can_multi_stack = false;
				if (!can_multi_stack || caster->SpawnId == player->BuffCasterId[buffslot])
				{
				OVERWRITE_SAME_SPELL_WITHOUT_REMOVING_FIRST:
					if (caster->Level >= buff->CasterLevel
						&& BSP_SpellAffectIndex(new_spell, 67) == 0  // Eye of Zomm
						&& BSP_SpellAffectIndex(new_spell, 101) == 0 // Complete Heal
						&& BSP_SpellAffectIndex(new_spell, 113) == 0)    // Summon Horse
					{
						// overwrite same spell_id without removing first
						*result_buffslot = buffslot;
						return buff;
					}
					else
					{
						*result_buffslot = -1;
						return 0;
					}
				}
				spell_id_already_affecting_target = true;
			}
		}
	}
	
	if (can_multi_stack)
	{
		if (spell_id_already_affecting_target)
		{
			int first_open_buffslot = -1;
			for (int i = 0; i < MaxSelectableBuffs; i++) {
				int buffslot = BSP_ToBuffSlot(i, StartBuffOffset, MaxSelectableBuffs); // [Patch:SongWindow] Translates the 'i' value to the right buffslot order
				EQBUFFINFO* buff = EQ_Character::GetBuff(player, buffslot);
				if (buff->BuffType)
				{
					if (spellid == buff->SpellId && player->SpawnInfo)
					{
						WORD buff_caster_id = player->BuffCasterId[buffslot];
						EQSPAWNINFO* buff_caster = nullptr;
						if (buff_caster_id && buff_caster_id < 0x1388u)
							buff_caster = EQPlayer::GetSpawn(buff_caster_id);
						if (!buff_caster || buff_caster == player->SpawnInfo)
						{
							*result_buffslot = buffslot;
							return buff; // overwrite same spell without removing first
						}
					}
				}
				else if (first_open_buffslot == -1)
				{
					first_open_buffslot = buffslot;
				}
			}
			if (first_open_buffslot != -1)
			{
				*result_buffslot = first_open_buffslot;
				return EQ_Character::GetBuff(player, first_open_buffslot);  // first empty slot, this is a DoT that will stack with itself because it's from another caster
			}
		}
	}

	if (false) // not entered here, jumped into with goto
	{
	STACK_OK_OVERWRITE_BUFF_IF_NEEDED:
		// if we have a result slot already, overwrite the result slot if something is there and it's not this spell_id
		if (*result_buffslot != -1)
		{
			EQBUFFINFO* buff = EQ_Character::GetBuff(player, *result_buffslot);
			if (!dry_run && buff->BuffType && spellid != buff->SpellId)
			{
				EQ_Character::RemoveBuff(player, buff, 0);
			}
			return buff;
		}
		if (!new_spell->IsBeneficial())
		{
			EQSPAWNINFO* self = player->SpawnInfo;
			if (self)
			{
				if (!self->IsGameMaster)
				{
					int curbuff_i = 0;
					int curbuff_slot = BSP_ToBuffSlot(curbuff_i, StartBuffOffset, MaxSelectableBuffs); // [Patch:SongWindow] Translates the 'curbuff_i' value to the right buffslot order
					
					while (1)
					{
						WORD buff_spell_id = EQ_Character::GetBuff(player, curbuff_slot)->SpellId;
						if (EQ_Spell::IsValidSpellIndex(buff_spell_id))
						{
							EQSPELLINFO* buff_spell = EQ_Spell::GetSpell(buff_spell_id);
							if (buff_spell && buff_spell->IsBeneficial()) // found a beneficial spell to overwrite
								break;
						}
						if (++curbuff_i >= MaxSelectableBuffs)
							return 0;
						curbuff_slot = BSP_ToBuffSlot(curbuff_i, StartBuffOffset, MaxSelectableBuffs); // [Patch:SongWindow] Translates the 'curbuff_i' value to the right buffslot order
					}
					if (!dry_run)
					{
						EQBUFFINFO* buff = EQ_Character::GetBuff(player, curbuff_slot); // overwriting a beneficial buff to make room for a detrimental one.
						EQ_Character::RemoveBuff(player, buff, 0);
					}
					*result_buffslot = curbuff_slot;
					goto RETURN_RESULT_SLOTNUM_194;
				}
			}
		}
		return 0;
	}

	while (1)
	{
		old_buff = EQ_Character::GetBuff(player, cur_slotnum7_buffslot);
		if (!old_buff->BuffType)
			goto STACK_OK4;

		old_buff_spell_id = old_buff->SpellId;
		if (EQ_Spell::IsValidSpellIndex(old_buff_spell_id))
		{
			old_spelldata = EQ_Spell::GetSpell(old_buff_spell_id);
			if (old_spelldata)
				break;
		}
		old_buff->BuffType = 0;
		old_buff->SpellId = -1;
		old_buff->CasterLevel = 0;
		old_buff->Ticks = 0;
		old_buff->Modifier = 0;
		old_buff->Counters = 0;
	STACK_OK4:
		no_slot_found_yet = *result_buffslot == -1;
	STACK_OK3:
		if (no_slot_found_yet)
		{
		STACK_OK2:
			*result_buffslot = cur_slotnum7_buffslot; // save first blank slot found
		}
	STACK_OK: // jump here when current buff and new buff don't interact to increment slot number and check next buff
		if (++cur_slotnum7 >= MaxSelectableBuffs)
		{
			goto STACK_OK_OVERWRITE_BUFF_IF_NEEDED;
		}
		cur_slotnum7_buffslot = BSP_ToBuffSlot(cur_slotnum7, StartBuffOffset, MaxSelectableBuffs); // [Patch:SongWindow] Translates the 'cur_slotnum7' value to the right buffslot order
	}
	if (is_bard_song && !old_spelldata->IsBardsong()) // [Patch:Main] Just checks 'is_bard_song' and not class
	{
		if (new_spell->IsBeneficial() && is_movement_effect && BSP_SpellAffectIndex(old_spelldata, SE_MovementSpeed) != 0
			|| new_spell->IsBeneficial() && is_movement_effect && BSP_SpellAffectIndex(old_spelldata, SE_Root) != 0)
		{
			goto BLOCK_BUFF_178; // [Patch:Main] This line isn't reachable, kept for consistency (formerly: "Bard Selos can't overwrite regular SoW type spell or rooting illusion")
		}

		// generally, bard songs stack with anything that's not a bard song
		if (is_bard_song)
			goto STACK_OK;
	}

	// [Patch:Main] Note - This section always reaches 'false', so SoW/Selos are not getting blocked here
	if (new_spell->IsBeneficial())
	{
		if (old_spelldata->IsBeneficial())
		{
			if (is_movement_effect)
			{
				if (BSP_SpellAffectIndex(old_spelldata, SE_MovementSpeed) != 0)
				{
					if (old_spelldata->IsBardsong() && !is_bard_song)
						goto BLOCK_BUFF_178; // regular SoW type spell can't overwrite bard Selos
				}
			}
		}
	}

	// below is a for loop that's kind of decomposed with gotos, comparing each effect slot
	effect_slot_num = 0;
	while (2)
	{
		BYTE old_buff_effect_id = old_spelldata->Attribute[effect_slot_num];
		if (old_buff_effect_id == SE_Blank) // blank effect slot in old spell, end of spell, don't check rest of slots
			goto STACK_OK;
		
		BYTE new_buff_effect_id = new_spell->Attribute[effect_slot_num];
		if (new_buff_effect_id == SE_Blank) // blank effect slot in new spell, end of spell, don't check rest of slots
			goto STACK_OK;

		if (new_buff_effect_id == SE_Lycanthropy || new_buff_effect_id == SE_Vampirism)
			goto BLOCK_BUFF_178;

		if ((!is_bard_song && old_spelldata->IsBardsong())
			|| old_buff_effect_id != new_buff_effect_id
			|| EQ_Spell::IsSPAIgnoredByStacking(new_buff_effect_id))
		{
			goto NEXT_ATTRIB_107; // ignore if different effect, ignored effect, or if the existing buff is a bard song
		}

		// at this point the effect ids are the same in this slot

		if (new_buff_effect_id == SE_CurrentHP || new_buff_effect_id == SE_ArmorClass)
		{
			if (new_spell->Base[effect_slot_num] >= 0)
				break;
			goto NEXT_ATTRIB_107; // if the new spell has a DoT or negative AC debuff in this effect slot, ignore for stacking
		}
		if (new_buff_effect_id == SE_CHA)
		{
			if (new_spell->Base[effect_slot_num] == 0 || old_spelldata->Base[effect_slot_num] == 0) // SE_CHA can be used as a spacer with 0 base
			{
			NEXT_ATTRIB_107:
				if (++effect_slot_num >= EQ_NUM_SPELL_EFFECTS)
					goto STACK_OK;
				continue;
			}
		}
		break;
	}

	// compare same effect id below

	if (new_spell->IsBeneficial() && (!old_spelldata->IsBeneficial() || BSP_SpellAffectIndex(old_spelldata, SE_Illusion) != 0)
		|| old_spelldata->Attribute[effect_slot_num] == SE_CompleteHeal // Donal's BP effect
		|| old_buff_spell_id >= 775 && old_buff_spell_id <= 785
		|| old_buff_spell_id >= 1200 && old_buff_spell_id <= 1250
		|| old_buff_spell_id >= 1900 && old_buff_spell_id <= 1924
		|| old_buff_spell_id == 2079 // ShapeChange65
		|| old_buff_spell_id == 2751 // Manaburn
		|| old_buff_spell_id == 756 // Resurrection Effects
		|| old_buff_spell_id == 757 // Resurrection Effect
		|| old_buff_spell_id == 836) // Diseased Cloud
	{
		goto BLOCK_BUFF_178;
	}

	old_effect_value = EQ_Character::CalcSpellEffectValue(player, old_spelldata, old_buff->CasterLevel, effect_slot_num, 0);
	new_effect_value = EQ_Character::CalcSpellEffectValue(player, new_spell, caster->Level, effect_slot_num, 0);

	if (spellid == 1620 || spellid == 1816 || spellid == 833 || old_buff_spell_id == 1814)
		new_effect_value = -1;
	if (old_buff_spell_id == 1620 || old_buff_spell_id == 1816 || old_buff_spell_id == 833 || old_buff_spell_id == 1814)
		old_effect_value = -1;
	old_effect_is_negative_or_zero = old_effect_value <= 0;
	if (old_effect_value >= 0)
	{
	OVERWRITE_INCREASE_WITH_DECREASE_137:
		if (!old_effect_is_negative_or_zero && new_effect_value < 0)
			goto OVERWRITE_INCREASE_WITH_DECREASE_166;
		bool is_disease_cloud = (spellid == 836);
		if (new_spell->Attribute[effect_slot_num] == SE_AttackSpeed)
		{
			if (new_effect_value < 100 && new_effect_value <= old_effect_value)
				goto OVERWRITE_150;
			if (old_effect_value <= 100)
				goto BLOCKED_BUFF_151;
			if (new_effect_value >= 100)
			{
			OVERWRITE_IF_GREATER_BLOCK_OTHERWISE_149:
				if (new_effect_value >= old_effect_value)
					goto OVERWRITE_150;
			BLOCKED_BUFF_151:
				if (!is_disease_cloud)
					goto BLOCK_BUFF_178;
				if (!new_spell->IsBeneficial() && !old_spelldata->IsBeneficial())
				{
					*result_buffslot = cur_slotnum7_buffslot;
					if (!dry_run && spellid != old_buff->SpellId)
						goto OVERWRITE_REMOVE_FIRST_170;
					goto RETURN_RESULT_SLOTNUM_194;
				}
				if (*result_buffslot == -1)
					goto STACK_OK2;
				no_slot_found_yet = EQ_Character::GetBuff(player, *result_buffslot)->BuffType == 0;
				goto STACK_OK3;
			}
		OVERWRITE_150:
			is_disease_cloud = 1;
			goto BLOCKED_BUFF_151;
		}
		old_effect_value_is_negative_or_zero = old_effect_value <= 0;
		if (old_effect_value < 0)
		{
			if (new_effect_value <= old_effect_value)
				goto OVERWRITE_150;
			old_effect_value_is_negative_or_zero = old_effect_value <= 0;
		}
		if (old_effect_value_is_negative_or_zero)
			goto BLOCKED_BUFF_151;
		goto OVERWRITE_IF_GREATER_BLOCK_OTHERWISE_149;
	}
	if (new_effect_value <= 0)
	{
		old_effect_is_negative_or_zero = old_effect_value <= 0;
		goto OVERWRITE_INCREASE_WITH_DECREASE_137;
	}
OVERWRITE_INCREASE_WITH_DECREASE_166:
	new_buff_effect_id2 = new_spell->Attribute[effect_slot_num];
	if (new_buff_effect_id2 != SE_MovementSpeed)
	{
		if (new_buff_effect_id2 != SE_CurrentHP || old_effect_value >= 0 || new_effect_value <= 0)
			goto USE_CURRENT_BUFF_SLOT;
	BLOCK_BUFF_178:
		*result_buffslot = -1;
		return 0;
	}
	if (new_effect_value >= 0)
		goto BLOCK_BUFF_178;
USE_CURRENT_BUFF_SLOT:
	*result_buffslot = cur_slotnum7_buffslot;
	if (!dry_run && spellid != old_buff->SpellId)
	{
	OVERWRITE_REMOVE_FIRST_170:
		EQBUFFINFO* buff = EQ_Character::GetBuff(player, cur_slotnum7_buffslot);
		EQ_Character::RemoveBuff(player, buff, 0);
		return buff;
	}
RETURN_RESULT_SLOTNUM_194:
	return EQ_Character::GetBuff(player, *result_buffslot);
}

// Entrypoint for Buff Patch
typedef _EQBUFFINFO* (__thiscall* EQ_FUNCTION_TYPE_EQCharacter__FindAffectSlot)(EQCHARINFO* this_ptr, WORD spellid, _EQSPAWNINFO* caster, DWORD* out_slot, int flag);
EQ_FUNCTION_TYPE_EQCharacter__FindAffectSlot EQCharacter__FindAffectSlot_Trampoline;
_EQBUFFINFO* __fastcall EQCharacter__FindAffectSlot_Detour(EQCHARINFO* player, int unused, WORD spellid, _EQSPAWNINFO* caster, DWORD* out_slot, int flag) {
	if (Rule_Buffstacking_Patch_Enabled) {
		return BSP_FindAffectSlot(player, spellid, caster, out_slot, flag);
	}
	return EQCharacter__FindAffectSlot_Trampoline(player, spellid, caster, out_slot, flag);
}

// ---------------------------------------------------------
// Buff Patch [Song Window]
// ---------------------------------------------------------

_EQBUFFINFO* GetStartBuffArray(bool song_buffs) {
	return song_buffs ? EQ_OBJECT_CharInfo->BuffsExt : EQ_OBJECT_CharInfo->Buff;
}
void MakeGetBuffReturnSongs(bool enabled) {
	ShortBuffSupport_ReturnSongBuffs = enabled;
}

// MaxBuffs is now increased when enabled (Rule_Max_Buffs)
typedef int(__thiscall* EQ_FUNCTION_TYPE_EQCharacter__GetMaxBuffs)(EQCHARINFO* this_ptr);
EQ_FUNCTION_TYPE_EQCharacter__GetMaxBuffs EQCharacter__GetMaxBuffs_Trampoline;
int __fastcall EQCHARACTER__GetMaxBuffs_Detour(EQCHARINFO* player, int unused)
{
	EQSPAWNINFO* spawn_info;
	if (player && (spawn_info = player->SpawnInfo) != 0) {
		if (spawn_info->Type == EQ_SPAWN_TYPE_PLAYER) {
			return Rule_Max_Buffs;
		}
		if (spawn_info->Type == EQ_SPAWN_TYPE_NPC) {
			return 30;
		}
	}
	return EQ_NUM_BUFFS;
}

// Helper to make ShortBuffWindow read from the song buff array.
typedef _EQBUFFINFO* (__thiscall* EQ_FUNCTION_TYPE_EQCharacter__GetBuff)(EQCHARINFO* this_char_info, int buff_slot);
EQ_FUNCTION_TYPE_EQCharacter__GetBuff EQCharacter__GetBuff_Trampoline;
_EQBUFFINFO* __fastcall EQCharacter__GetBuff_Detour(EQCHARINFO* player, int unused, WORD buff_slot) {
	if (ShortBuffSupport_ReturnSongBuffs && buff_slot < 15) {
		buff_slot += 15;
	}
	return EQCharacter__GetBuff_Trampoline(player, buff_slot);
}

// Hook that removes buffs or shows spell info when clicking the song window, and shows tooltips on mouseover
int __fastcall CBuffWindow__WndNotification_Detour(CBuffWindow* self, int unused, PEQCBUFFBUTTONWND sender, int type, int a4)
{
	// Shared hook with CBuffWindow
	// Use the right buff slot offset based on the window.
	bool is_song_window = (self == GetShortDurationBuffWindow());
	int start_buff_index = is_song_window ? 15 : 0;

	if (type != 1)
	{
		if (type != 23 && type != 25)
			return CSidlScreenWnd::WndNotification(self, sender, type, a4);
	LABEL_11:
		MakeGetBuffReturnSongs(is_song_window);
		self->HandleSpellInfoDisplay(sender);
		MakeGetBuffReturnSongs(false);
		return CSidlScreenWnd::WndNotification(self, sender, type, a4);
	}
	if (AltPressed())
		goto LABEL_11;
	for (int i = 0; i < EQ_NUM_BUFFS; i++) {
		if (self->Data.BuffButtonWnd[i] == sender) {
			if (EQ_Character::IsValidAffect(EQ_OBJECT_CharInfo, i + start_buff_index))
				EQ_Character::RemoveMyAffect(EQ_OBJECT_CharInfo, i + start_buff_index);
			return CSidlScreenWnd::WndNotification(self, sender, type, a4);
		}
	}
	return CSidlScreenWnd::WndNotification(self, sender, type, a4);
}

CShortBuffWindow* GetShortDurationBuffWindow() {
	return ShortBuffWindow;
}

void ShortBuffWindow_InitUI(CDisplay* cdisplay) {

	if (ShortBuffWindow)
		return;

	CShortBuffWindow* wnd = reinterpret_cast<CShortBuffWindow*>(HeapAlloc(*(HANDLE*)0x80B420, 0, sizeof(_EQCBUFFWINDOW)));
	if (wnd) {
		memset(wnd, 0, sizeof(_EQCBUFFWINDOW));

		// Need to patch the instruction to load our name 'ShortDurationBuffWindow' instead of 'BuffWindow'
		BYTE orig_inst[5];
		BYTE new_inst[5] = { 0x68, 0, 0 , 0, 0 };
		*(uintptr_t*)&new_inst[1] = (uintptr_t)CShortBuffWindow::NAME;

		PatchSwap(0x00408D5A, new_inst, 5, orig_inst);
		CBuffWindow::Consutrctor(wnd);
		PatchSwap(0x00408D5A, orig_inst, 5);

		ShortBuffWindow = wnd;
	}
}
void ShortBuffWindow_CleanUI() {
	if (ShortBuffWindow)
	{
		if (ShortBuffWindow->IsVisibile())
			ShortBuffWindow->Deactivate();
		if (ShortBuffWindow->HasCustomVTable())
			ShortBuffWindow->DeleteCustomVTable();
		ShortBuffWindow->Destroy();
	}
	ShortBuffWindow = nullptr;
}
void ShowBuffWindow_ActivateUI(char c) {
	if (ShortBuffWindow) {
		ShortBuffWindow->LoadIniInfo();
		ShortBuffWindow->Activate();
	}
}
void ShowBuffWindow_DeactivateUI() {
	if (ShortBuffWindow && ShortBuffWindow->IsVisibile()) {
		ShortBuffWindow->StoreIniInfo();
		ShortBuffWindow->Deactivate();
	}
}

void ApplySongWindowBytePatches() {
	// HandleWorldMessage (OP_Buff): Has a hardcoded for-loop of only 15 buffs. Switching to 30.
	// * '0x004E9F8E cmp 15' -> 'cmp 30'
	// [0x83 0xFF 0x0F] -> [0x83 0xFF 0x1E]
	BYTE patch[1] = { 0x1E };
	int address = 0x004E9F8E + 2; 
	PatchSwap(address, patch, 1);
}

// ---------------------------------------------------------------------------------------
// Buff Patch [End]
// ---------------------------------------------------------------------------------------

// ---------------------------------------------------------------------------------------
// Appearance Fixes/Support
// - Helmet/Weapon Tint Support
// ---------------------------------------------------------------------------------------

constexpr BYTE kMaterialSlotHead = 0;
constexpr BYTE kMaterialSlotPrimary = 7;
constexpr BYTE kMaterialSlotSecondary = 8; // Shared with 'ranged'

constexpr WORD kMaterialNone = 0;
constexpr WORD kMaterialLeather = 1;
constexpr WORD kMaterialChain = 2;
constexpr WORD kMaterialPlate = 3;
constexpr WORD kMaterialVeliousHelm = 240;
constexpr WORD kMaterialVeliousHelmAlternate = 241; // A couple races support alternate helms

// We install 'Bald' variation of heads with ID 05: "{racetag}HE05_DMSPRITEDEF". We swap to this head only when wearing a Velious Helm, to ensure hair clipping is fixed.
constexpr WORD kMaterialBaldHead = 5;
constexpr char kHumanFemaleBaldHead[] = "HUFHE05_DMSPRITEDEF"; // todo
constexpr char kBarbarianFemaleBaldHead[] = "BAFHE05_DMSPRITEDEF"; // todo
constexpr char kEruditeFemaleBaldHead[] = "ERFHE05_DMSPRITEDEF"; // todo
constexpr char kEruditeMaleBaldHead[] = "ERMHE05_DMSPRITEDEF"; // done
constexpr char kWoodElfFemaleBaldHead[] = "ELFHE05_DMSPRITEDEF"; // todo
constexpr char kDarkElfFemaleBaldHead[] = "DAFHE05_DMSPRITEDEF"; // todo

constexpr DWORD kColorNone = 0;
constexpr DWORD kColorDefault = 0x00FFFFFF;

BYTE BYTE_BALD_HEAD[1] = { kMaterialBaldHead };
BYTE BYTE_NORMAL_HEAD[1] = { (BYTE)kMaterialNone };

DWORD block_outbound_wearchange = 0;

bool DetectHelmFixesComplete = false;
bool UseHumanFemaleFix = false;
bool UseBarbarianFemaleFix = false;
bool UseEruditeMaleFix = false;
bool UseEruditeFemaleFix = false;
bool UseWoodElfFemaleFix = false;
bool UseDarkElfFemaleFix = false;

// Helper function. Converts Velious Helms to their common values.
// We only send the canonical values to the server and other players.
// - [5xx/6xx] -> [240] Swaps our racial Velious head model IT### back to the generic '240' value used by all Velious helms.
WORD ToCanonicalHelmMaterial(WORD material, WORD race)
{
	if ((race >= 1 && race <= 12) || race == 128 || race == 130)
	{
		switch (material)
		{
			// Vah Shir have their own material IDs when they equip leather/chain/plate helms, but no custom helm.
		case 661: // VAH (F) Leather Helm
		case 666: // VAH (M) Leather Helm
			return kMaterialLeather; // (1)
		case 662: // VAH (F) Chain Helm
		case 667: // VAH (M) Chain Helm
			return kMaterialChain; // (2)
		case 663: // VAH (F) Plate Helm
		case 668: // VAH (M) Plate Helm
			return kMaterialPlate; // (3)

			// Converts all the race-specific Velious Helm IT### numbers to the common 240 value
		case 665: // vah
		case 660: // vah
		case 627: // hum
		case 620: // hum
		case 537: // bar
		case 530: // bar
		case 570: // eru
		case 575: // eru
		case 565: // elf
		case 561: // elf
		case 605: // hie
		case 600: // hie
		case 545: // def
		case 540: // def
		case 595: // hef
		case 590: // hef
		case 557: // dwf
		case 550: // dwf
		case 655: // trl
		case 650: // trl
		case 645: // ogr
		case 640: // ogr
		case 615: // hlf
		case 610: // hlf
		case 585: // gnm
		case 580: // gnm
		case 635: // iks
		case 630: // iks
			if (race == 130) // vah
				return kMaterialPlate;
			return kMaterialVeliousHelm;
		case 641: // OGR (F) Alternate Helm (Barbarian/RZ look)
		case 646: // OGR (M) Alternate Helm (Barbarian/RZ look)
			if (race == 10) // ogre
				return kMaterialVeliousHelmAlternate;
			return kMaterialVeliousHelm;
		}
	}
	return material;
}

bool HelmHelperIsEnabled(char* key)
{
	char szResult[255];
	char szDefault[255];
	sprintf(szDefault, "%s", "FALSE");
	DWORD error = GetPrivateProfileStringA("Defaults", key, szDefault, szResult, 255, "./eqclient.ini");
	if (strcmp(szResult, "TRUE") == 0)
		return true;
	return false;
}

bool DetectHelmFixes()
{
	if (DetectHelmFixesComplete)
		return true;

	if (!Graphics::IsWorldInitialized())
		return false;

	// Check if a known-good value is loaded before continuing
	int* sprite_definition = Graphics::t3dGetPointerFromDictionary("ELFHE00_DMSPRITEDEF");
	if (!sprite_definition)
		return false;

	bool AllLuclinPcModelsOff = HelmHelperIsEnabled("AllLuclinPcModelsOff");
	bool UseLuclinHumanFemale = HelmHelperIsEnabled("UseLuclinHumanFemale");
	bool UseLuclinBarbarianFemale = HelmHelperIsEnabled("UseLuclinBarbarianFemale");
	bool UseLuclinEruditeFemale = HelmHelperIsEnabled("UseLuclinEruditeFemale");
	bool UseLuclinEruditeMale = HelmHelperIsEnabled("UseLuclinEruditeMale");
	bool UseLuclinWoodElfFemale = HelmHelperIsEnabled("UseLuclinWoodElfFemale");
	bool UseLuclinDarkElfFemale = HelmHelperIsEnabled("UseLuclinDarkElfFemale");
	UseHumanFemaleFix     = (AllLuclinPcModelsOff || !UseLuclinHumanFemale)     && Graphics::t3dGetPointerFromDictionary(kHumanFemaleBaldHead);
	UseBarbarianFemaleFix = (AllLuclinPcModelsOff || !UseLuclinBarbarianFemale) && Graphics::t3dGetPointerFromDictionary(kBarbarianFemaleBaldHead);
	UseEruditeFemaleFix   = (AllLuclinPcModelsOff || !UseLuclinEruditeFemale)   && Graphics::t3dGetPointerFromDictionary(kEruditeFemaleBaldHead);
	UseEruditeMaleFix     = (AllLuclinPcModelsOff || !UseLuclinEruditeMale)     && Graphics::t3dGetPointerFromDictionary(kEruditeMaleBaldHead);
	UseWoodElfFemaleFix   = (AllLuclinPcModelsOff || !UseLuclinWoodElfFemale)   && Graphics::t3dGetPointerFromDictionary(kWoodElfFemaleBaldHead);
	UseDarkElfFemaleFix   = (AllLuclinPcModelsOff || !UseLuclinDarkElfFemale)   && Graphics::t3dGetPointerFromDictionary(kDarkElfFemaleBaldHead);
	DetectHelmFixesComplete = true;
	return true;
}

bool IsHelmPatchedOldModel(WORD race, BYTE gender)
{
	if (!DetectHelmFixesComplete)
	{
		DetectHelmFixes(); // Have to lazy-load this here because this is reached before OnZone() is called during initial login.
	}

	// Bugged male races
	if (gender == 0)
	{
		// Erudite
		return race == 3 ? UseEruditeMaleFix : false;
	}

	// Bugged female races
	if (gender == 1)
	{
		switch (race)
		{
		case 1: // Human
			return UseHumanFemaleFix;
		case 2: // Barbarian
			return UseBarbarianFemaleFix;
		case 3: // Erudite
			return UseEruditeFemaleFix;
		case 4: // Wood Elf
			return UseWoodElfFemaleFix;
		case 6: // Dark Elf
			return UseDarkElfFemaleFix;
		}
	}

	return false;
}

typedef int(__thiscall* EQ_FUNCTION_TYPE_SwapHead)(int* cDisplay, EQSPAWNINFO* entity, int new_material, int old_material, DWORD color, bool from_server);
EQ_FUNCTION_TYPE_SwapHead SwapHead_Trampoline;
int __fastcall SwapHead_Detour(int* cDisplay, int unused_edx, EQSPAWNINFO* entity, int new_material, int old_material_or_head, DWORD color, bool from_server)
{
	bool use_bald_head = false; // On races with buggy Velious helms, we will try to use the bald head underneath the helm to fix clipping (see 3a).

	if (entity->Texture == 0xFF) // Most logic only needs to apply on playable races.
	{
		// (1) Fixes the old head from getting desync'd/stuck. We can manually detect the current head which ensures that SwapHead always works (requires the old head value to be accurate).
		old_material_or_head = EQPlayer::GetHeadID(entity, old_material_or_head);

		// (2a) Fix broken Velious races by using a special head with no hair/hood graphics underneath their helmet. This stops their hair/hood clipping through the helm.
		use_bald_head = new_material >= kMaterialVeliousHelm && IsHelmPatchedOldModel(entity->Race, entity->Gender);
		if (use_bald_head)
		{
			PatchSwap(0x4A1C65 + 1, BYTE_BALD_HEAD, 1); // Changes default head 0 -> 5
		}

		// (3) Fixes a bug that double-sends packets on materials below 240. Suppresses the extra packet (which also contains the wrong value).
		if (new_material < kMaterialVeliousHelm || block_outbound_wearchange > 0)
		{
			from_server = true; // This flag only controls whether the client generates a WearChange packet after swapping gear (true = local only, false = send packet)
		}

		// (4) Save the helmet color for tinting. SwapHead() calls SwapModel(), where we apply the tint. But the default SwapHead() saves the color too late, after calling SwapModel().
		EQPlayer::SaveMaterialColor(entity, kMaterialSlotHead, color);
	}

	// Call SwapHead()
	int result = SwapHead_Trampoline(cDisplay, entity, new_material, old_material_or_head, color, from_server);

	// (5) Fixes SwapHead() to save material values correctly when material >255. The original method only sets the lo-byte, but the storage supports uint16.
	entity->EquipmentMaterialType[kMaterialSlotHead] = new_material;

	// (2b) Unpatch the Change from (2a)
	if (use_bald_head)
	{
		PatchSwap(0x4A1C65 + 1, BYTE_NORMAL_HEAD, 1); // Changes default head 5 -> 0
	}

	return result;
}

// Called when changing armor textures (head chest arms legs feet hands).
// On character select screen, also called for weapons slots.
typedef void(__thiscall* EQ_FUNCTION_TYPE_WearChangeArmor)(int* cDisplay, EQSPAWNINFO* entity, int wear_slot, WORD new_material, WORD old_material, DWORD colors, bool from_server);
EQ_FUNCTION_TYPE_WearChangeArmor WearChangeArmor_Trampoline;
void __fastcall WearChangeArmor_Detour(int* cDisplay, int unused_edx, EQSPAWNINFO* entity, BYTE wear_slot, WORD new_material, WORD old_material, DWORD colors, bool from_server)
{
	int block_wearchange = 0;
	if (from_server && entity->Texture == 0xFF && entity == EQ_OBJECT_PlayerSpawn)
	{
		// Inbound WearChanges from the server shouldn't generate a response. However, the client doesn't respect 'from_server' flag on some helmets and replies anyway.
		block_wearchange = 1;

		// Update tint cache (This line is needed for character select scren tints)
		EQPlayer::SaveMaterialColor(entity, wear_slot, colors);
	}

	block_outbound_wearchange += block_wearchange;
	WearChangeArmor_Trampoline(cDisplay, entity, wear_slot, new_material, old_material, colors, from_server);
	block_outbound_wearchange -= block_wearchange;
}

typedef int(__thiscall* EQ_FUNCTION_TYPE_SwapModel)(int* cdisplay, EQSPAWNINFO* entity, int wear_slot, char* ITstr, int from_server);
EQ_FUNCTION_TYPE_SwapModel SwapModel_Trampoline;
int __fastcall SwapModel_Detour(int* cDisplay, int unused, EQSPAWNINFO* entity, BYTE wear_slot, char* ITstr, int from_server)
{
	int material = (ITstr && strlen(ITstr) > 2) ? atoi(&ITstr[2]) : 0;
	bool is_weapon_slot = wear_slot == kMaterialSlotPrimary || wear_slot == kMaterialSlotSecondary;
	bool is_tint_slot = is_weapon_slot || (wear_slot == kMaterialSlotHead && entity->Texture == 0xFF);

	if (from_server == 0 && is_weapon_slot && entity == EQ_OBJECT_PlayerSpawn && EQ_OBJECT_CharInfo)
	{
		// This is reached when an item was swapped by the user equipping a new item through the UI.
		// We aren't given the color of the item in this scenario, so we have to look it up by matching the IT# to the equipped item in primary/secondary/range slot.
		// In all other Scenarios, we already know the color because we got an OP_WearChange event, so we can skip this logic.
		EQINVENTORY& inv = EQ_OBJECT_CharInfo->Inventory;
		if (material == kMaterialNone)
		{
			EQPlayer::SaveMaterialColor(entity, wear_slot, kColorNone);
		}
		else if (wear_slot == kMaterialSlotPrimary)
		{
			EQPlayer::SaveMaterialColor(entity, wear_slot, inv.Primary ? inv.Primary->Common.Color : kColorNone);
		}
		else if (EQ_Item::GetItemMaterial(inv.Secondary) == material)
		{
			EQPlayer::SaveMaterialColor(entity, wear_slot, inv.Secondary ? inv.Secondary->Common.Color : kColorNone);
		}
		else if (EQ_Item::GetItemMaterial(inv.Ranged) == material)
		{
			EQPlayer::SaveMaterialColor(entity, wear_slot, inv.Ranged ? inv.Ranged->Common.Color : kColorNone);
		}
	}

	int result = SwapModel_Trampoline(cDisplay, entity, wear_slot, ITstr, from_server);

	// After models are swapped, apply tint to the Helm and Weapon slots.
	if (material > kMaterialNone && is_tint_slot)
	{
		DWORD color = entity->EquipmentMaterialColor[wear_slot];
		DWORD tint = color == kColorNone ? kColorDefault : color;
		EQDAGINFO* dag = EQPlayer::GetDag(entity, wear_slot);
		if (dag)
		{
			CDisplay::SetDagSpriteTint(dag, tint);
		}
		if (wear_slot == kMaterialSlotSecondary && entity->ActorInfo && entity->ActorInfo->DagShieldPoint) // Also tint shields
		{
			CDisplay::SetDagSpriteTint(entity->ActorInfo->DagShieldPoint, tint);
		}
	}

	return result;
}

// Callback for server WearChange packets. It immediately calls HandleWearChangeArmor for non-weapon slots.
bool Handle_In_OP_WearChange(WearChange_Struct* wc)
{
	if (!wc)
		return false;

	EQSPAWNINFO* entity = EQPlayer::GetSpawn(wc->spawn_id);
	if (!entity)
		return false;

	// Weapon color is not passed from OP_WearChange to any called method, so we have to save it from here.
	if (wc->wear_slot_id == kMaterialSlotPrimary || wc->wear_slot_id == kMaterialSlotSecondary)
	{
		EQPlayer::SaveMaterialColor(entity, wc->wear_slot_id, wc->color);
	}
	return false;
}

bool Handle_Out_OP_WearChange(WearChange_Struct* wc)
{
	if (!wc)
		return false;

	EQSPAWNINFO* self = EQ_OBJECT_PlayerSpawn;
	if (!self)
		return false;

	if (wc->wear_slot_id == kMaterialSlotHead)
	{
		if (block_outbound_wearchange > 0)
			return true; // Stop processing this OP_WearChange, preventing the message from being sent.

		if (self->Texture == 0xFF && wc->material >= kMaterialVeliousHelm)
		{
			// Ensure helm tint is sent for custom helms
			wc->material = ToCanonicalHelmMaterial(wc->material, self->Race);
			wc->color = self->EquipmentMaterialColor[kMaterialSlotHead];
		}
	}
	else if (wc->wear_slot_id == kMaterialSlotPrimary || wc->wear_slot_id == kMaterialSlotSecondary)
	{
		// Fixes outbound weapons to include the current tint
		if (wc->material > 0)
			wc->color = self->EquipmentMaterialColor[wc->wear_slot_id];
		else
			wc->color = 0;
	}
	return false; // Continue processing this OP_WearChange, sending the message.
}

void ApplyTintPatches()
{
	// GetVeliousHelmMaterialIT_4A1512(entity, material, *show_hair)
	// - (1) Disables hair becoming invisible on the shared default head. Prevents "show_hair = false" happening with Velious helms.
	PatchNopByRange(0x4A159B, 0x4A159D); // '*show_hair = 0' -> No-OP
	PatchNopByRange(0x4A16D2, 0x4A16D4); // '*show_hair = 0' -> No-OP
	// - (2) Enables Velious Helms showing on Character Select. Prevents returning early if char_info is null.
	PatchNopByRange(0x4A152B, 0x4A1533); // 'if (!char_info) return 3'; -> No-OP
	PatchNopByRange(0x4A153E, 0x4A154B); // 'if ((char_info->Unknown0D3C & 0x1E) == 0) return 3;' -> No-OP

	// ChangeDag()
	// - Unlocks proper tinting for IT# model helms/weapons below IT# number 1000:
	// - IT# models under ID 1000 used shared memory in their tint storage, so setting the tint on one model affected all models in the zone.
	DWORD value1 = 1;
	PatchA((void*)(0x4B094E + 3), (const void*)&value1, sizeof(DWORD));
	PatchA((void*)(0x4B099E + 3), (const void*)&value1, sizeof(DWORD));
	
}

// ---------------------------------------------------------------------------------------
// Tint Support [End]
// ---------------------------------------------------------------------------------------

DWORD gmfadress = 0;
DWORD wpsaddress = 0;
DWORD swAddress = 0;
DWORD cwAddress = 0;
DWORD swlAddress = 0;
DWORD uwAddress = 0;

PVOID pHandler;
bool bInitalized=false;

void CheckPromptUIChoice()
{
	char szResult[255];
	char szDefault[255];
	sprintf(szDefault, "%s", "NONE");
	DWORD error = GetPrivateProfileStringA("Defaults", "OldUI", szDefault, szResult, 255, "./eqclient.ini");
	if (strcmp(szResult, "NONE") == 0) // File not found
	{
		int Result = MessageBox(EQhWnd, "This server supports running both the Stone (Pre-Luclin) UI, and the more modern Luclin UI.\n Would you like to use the Luclin UI? This can later be adjusted ingame by typing /oldui.", "EverQuest", MB_YESNO);
		if (Result == IDYES)
		{
			WritePrivateProfileStringA_tramp("Defaults", "OldUI", "FALSE", "./eqclient.ini");
		}
		else
		{
			WritePrivateProfileStringA_tramp("Defaults", "OldUI", "TRUE", "./eqclient.ini");
		}

	}
}


void CheckClientMiniMods()
{
	char szResult[255];
	char szDefault[255];
	sprintf(szDefault, "%s", "NONE");
	DWORD error = GetPrivateProfileStringA("Defaults", "EnableBrownSkeletonHack", szDefault, szResult, 255, "./eqclient.ini");
	if (strcmp(szResult, "FALSE") == 0) // False
	{
		g_bEnableBrownSkeletons = false;
	}
	else if (strcmp(szResult, "NONE") == 0) // Not found
	{
		WritePrivateProfileStringA_tramp("Defaults", "EnableBrownSkeletonHack", "FALSE", "./eqclient.ini");
	}
	else // any other value (1, true, potato)
	{
		g_bEnableBrownSkeletons = true;
	}


	error = GetPrivateProfileStringA("Defaults", "EnableExtendedNameplateDistance", szDefault, szResult, 255, "./eqclient.ini");
	if (strcmp(szResult, "FALSE") == 0) // False
	{
		g_bEnableExtendedNameplates = false;
	}
	else if (strcmp(szResult, "NONE") == 0) // Not found
	{
		g_bEnableExtendedNameplates = false;
		WritePrivateProfileStringA_tramp("Defaults", "EnableExtendedNameplateDistance", "FALSE", "./eqclient.ini");
	}
	else
	{
		g_bEnableExtendedNameplates = true;
	}

	error = GetPrivateProfileStringA("Defaults", "EnableClassicMusic", szDefault, szResult, 255, "./eqclient.ini");
	if (strcmp(szResult, "FALSE") == 0) // False
	{
		g_bEnableClassicMusic = false;
	}
	else if (strcmp(szResult, "NONE") == 0) // Not found
	{
		g_bEnableClassicMusic = false;
		WritePrivateProfileStringA_tramp("Defaults", "EnableClassicMusic", "FALSE", "./eqclient.ini");
	}
	else
	{
		g_bEnableClassicMusic = true;
		EzDetour(0x00550AF8, &Eqmachooks::CEQMusicManager__Set_Detour, &Eqmachooks::CEQMusicManager__Set_Trampoline);
		EzDetour(0x004D54C1, &Eqmachooks::CEQMusicManager__Play_Detour, &Eqmachooks::CEQMusicManager__Play_Trampoline);
		//EzDetour(0x004D518B, &Eqmachooks::CEQMusicManager__WavPlay_Detour, &Eqmachooks::CEQMusicManager__WavPlay_Trampoline);
	}

	error = GetPrivateProfileStringA("Defaults", "SongWindowAutoHide", szDefault, szResult, 255, "./eqclient.ini");
	if (strcmp(szResult, "TRUE") == 0) // True
	{
		g_bSongWindowAutoHide = true;
	}
	else if (strcmp(szResult, "NONE") == 0) // Not found
	{
		g_bSongWindowAutoHide = false;
		WritePrivateProfileStringA_tramp("Defaults", "SongWindowAutoHide", "FALSE", "./eqclient.ini");
	}
	else // Default off
	{
		g_bSongWindowAutoHide = false;
	}
}

void InitHooks()
{
	//bypass filename req
	const char test3[] = { 0x90, 0x90, 0x90, 0x90, 0x90, 0x90,0x90, 0xEB, 0x1B, 0x90, 0x90, 0x90, 0x90 };
	PatchA((DWORD*)0x005595A7, &test3, sizeof(test3));

	HMODULE eqgfx_dll = LoadLibraryA("eqgfx_dx8.dll");
	if (eqgfx_dll)
	{
		HINSTANCE heqGfxMod = GetModuleHandle("eqgfx_dx8.dll");
		if (heqGfxMod)
		{
			_s3dSetStringSpriteYonClip s3dSetStringSpriteYonClip = (_s3dSetStringSpriteYonClip)GetProcAddress(heqGfxMod, "s3dSetStringSpriteYonClip");
			if (s3dSetStringSpriteYonClip)
			{
				(_s3dSetStringSpriteYonClip)s3dSetStringSpriteYonClip_Trampoline = (_s3dSetStringSpriteYonClip)DetourFunction((PBYTE)s3dSetStringSpriteYonClip, (PBYTE)s3dSetStringSpriteYonClip_Detour);
			}
			_FastMathFunction ot3dFastCosine = (_FastMathFunction)GetProcAddress(heqGfxMod, "t3dFloatFastCosine");
			if (ot3dFastCosine)
			{
				(_FastMathFunction)GetFastCosine_Trampoline = (_FastMathFunction)DetourFunction((PBYTE)ot3dFastCosine, (PBYTE)t3dFastCosine_Detour);
			}

			_FastMathFunction ot3dFastSine = (_FastMathFunction)GetProcAddress(heqGfxMod, "t3dFloatFastSine");
			if (ot3dFastSine)
			{
				(_FastMathFunction)GetFastSine_Trampoline = (_FastMathFunction)DetourFunction((PBYTE)ot3dFastSine, (PBYTE)t3dFastSine_Detour);
			}

			_FastMathFunction ot3dFastCotangent = (_FastMathFunction)GetProcAddress(heqGfxMod, "t3dFloatFastCotangent");
			if (ot3dFastCotangent)
			{
				(_FastMathFunction)GetFastCotangent_Trampoline = (_FastMathFunction)DetourFunction((PBYTE)ot3dFastCotangent, (PBYTE)t3dFastCotangent_Detour);
			}

			_CalculateAccurateCoefficientsFromHeadingPitchRoll ot3dCalculateCoefficientsFromHeadingPitchRoll = (_CalculateAccurateCoefficientsFromHeadingPitchRoll)GetProcAddress(heqGfxMod, "t3dCalculateCoefficientsFromHeadingPitchRoll");
			if (ot3dCalculateCoefficientsFromHeadingPitchRoll)
			{
				(_CalculateAccurateCoefficientsFromHeadingPitchRoll)CalculateCoefficientsFromHeadingPitchRoll_Trampoline = (_CalculateAccurateCoefficientsFromHeadingPitchRoll)DetourFunction((PBYTE)ot3dCalculateCoefficientsFromHeadingPitchRoll, (PBYTE)CalculateCoefficientsFromHeadingPitchRoll_Detour);
			}

			_CalculateAccurateCoefficientsFromHeadingPitchRoll ot3dCCalculateHeadingPitchRollFromCoefficients = (_CalculateAccurateCoefficientsFromHeadingPitchRoll)GetProcAddress(heqGfxMod, "t3dCalculateHeadingPitchRollFromCoefficients");
			if (ot3dCCalculateHeadingPitchRollFromCoefficients)
			{
				(_CalculateAccurateCoefficientsFromHeadingPitchRoll)CalculateHeadingPitchRollFromCoefficients_Trampoline = (_CalculateAccurateCoefficientsFromHeadingPitchRoll)DetourFunction((PBYTE)ot3dCCalculateHeadingPitchRollFromCoefficients, (PBYTE)CalculateHeadingPitchRollFromCoefficients_Detour);
			}
			//org_fix16Tangent = (DWORD)GetProcAddress(heqGfxMod, "t3dAngleArcTangentFix16");

			org_nonFastCos = (DWORD)GetProcAddress(heqGfxMod, "t3dFloatCosine");
			org_nonFastSin = (DWORD)GetProcAddress(heqGfxMod, "t3dFloatSine");
			org_nonFastCotangent = (DWORD)GetProcAddress(heqGfxMod, "t3dFloatCotangent");
			org_calculateAccurateCoefficientsFromHeadingPitchRoll = (DWORD)GetProcAddress(heqGfxMod, "t3dCalculateAccurateCoefficientsFromHeadingPitchRoll");
			org_calculateAccurateHeadingPitchRollFromCoefficients = (DWORD)GetProcAddress(heqGfxMod, "t3dCalculateAccurateHeadingPitchRollFromCoefficients");
			//_FastMathFunction ot3dFastCotangent = (_FastMathFunction)GetProcAddress(heqGfxMod, "t3dFloatFastCotangent");
			//if (ot3dFastCotangent)
			//{
			//	(_FastMathFunction)GetFastCotangent_Trampoline = (_FastMathFunction)DetourFunction((PBYTE)ot3dFastCotangent, (PBYTE)t3dFastCotangent_Detour);
			//}

			_GetCpuSpeed2 cpuSpeed2 = (_GetCpuSpeed2)GetProcAddress(heqGfxMod, "GetCpuSpeed2");
			if (cpuSpeed2)
			{
				(_GetCpuSpeed2)GetCpuSpeed2_Trampoline = (_GetCpuSpeed2)DetourFunction((PBYTE)cpuSpeed2, (PBYTE)GetCpuSpeed2_Detour);
			}

			_GetCpuSpeed2 cpuSpeed3 = (_GetCpuSpeed2)GetProcAddress(heqGfxMod, "GetCpuSpeed3");
			if (cpuSpeed3)
			{
				(_GetCpuSpeed2)GetCpuSpeed1_Trampoline = (_GetCpuSpeed2)DetourFunction((PBYTE)cpuSpeed3, (PBYTE)GetCpuSpeed2_Detour);
			}
		}
	}
	PatchSaveBypass();
	//heqwMod
	HMODULE hkernel32Mod = GetModuleHandle("kernel32.dll");
	gmfadress = (DWORD)GetProcAddress(hkernel32Mod, "GetModuleFileNameA");
	wpsaddress = (DWORD)GetProcAddress(hkernel32Mod, "WritePrivateProfileStringA");
	HMODULE huser32Mod = GetModuleHandleA("user32.dll");

	swAddress = (DWORD)GetProcAddress(huser32Mod, "ShowWindow");
	cwAddress = (DWORD)GetProcAddress(huser32Mod, "CreateWindowExA");
	swlAddress = (DWORD)GetProcAddress(huser32Mod, "SetWindowLong");
	EzDetour(0x004F2ED0, SendExeChecksum_Detour, SendExeChecksum_Trampoline);
	EzDetour(0x004AA8BC, &Eqmachooks::CDisplay__Render_World_Detour, &Eqmachooks::CDisplay__Render_World_Trampoline);
	EzDetour(cwAddress, CreateWindowExA_Detour, CreateWindowExA_Trampoline);
	//here to fix the no items on corpse bug - eqmule
	EzDetour(0x004E829F, &Eqmachooks::CEverQuest__HandleWorldMessage_Detour, &Eqmachooks::CEverQuest__HandleWorldMessage_Trampoline);
	CEverQuest__SendMessage_Trampoline = (EQ_FUNCTION_TYPE_CEverQuest__SendMessage)DetourFunction((PBYTE)0x54E51A, (PBYTE)CEverQuest__SendMessage_Detour);
	EzDetour(gmfadress, GetModuleFileNameA_detour, GetModuleFileNameA_tramp);
	EzDetour(wpsaddress, WritePrivateProfileStringA_detour, WritePrivateProfileStringA_tramp);

	// Supports additional labels (Song Window, for now). Zeal handles most others.
	GetLabelFromEQ_Trampoline = (EQ_FUNCTION_TYPE_GetLabelFromEQ)DetourFunction((PBYTE)0x436680, (PBYTE)GetLabelFromEQ_Detour);

	// Helper hooks that run callbacks
	EnterZone_Trampoline = (EQ_FUNCTION_TYPE_EnterZone)DetourFunction((PBYTE)0x53D2C4, (PBYTE)EnterZone_Detour); // OnZone callbacks
	HandleSpawnAppearanceMessage_Trampoline = (EQ_FUNCTION_TYPE_HandleSpawnAppearanceMessage)DetourFunction((PBYTE)0x004DF52A, (PBYTE)HandleSpawnAppearanceMessage_Detour); // OnSpawnAppearance(256) callbacks
	InitGameUI_Trampoline = (EQ_FUNCTION_TYPE_InitGameUI)DetourFunction((PBYTE)0x004a60b5, (PBYTE)InitGameUI_Detour);
	CleanUpUI_Trampoline = (EQ_FUNCTION_TYPE_CleanUpUI)DetourFunction((PBYTE)0x004A6EBC, (PBYTE)CleanUpUI_Detour);
	ActivateUI_Trampoline = (EQ_FUNCTION_TYPE_ActivateUI)DetourFunction((PBYTE)0x004A741B, (PBYTE)ActivateUI_Detour);
	DeactivateUI_Trampoline = (EQ_FUNCTION_TYPE_DeactivateUI)DetourFunction((PBYTE)0x4A7705, (PBYTE)DeactivateUI_Detour);
	
	EQMACMQ_REAL_CBuffWindow__RefreshBuffDisplay = (EQ_FUNCTION_TYPE_CBuffWindow__RefreshBuffDisplay)DetourFunction((PBYTE)EQ_FUNCTION_CBuffWindow__RefreshBuffDisplay, (PBYTE)EQMACMQ_DETOUR_CBuffWindow__RefreshBuffDisplay);
	EQMACMQ_REAL_CBuffWindow__PostDraw = (EQ_FUNCTION_TYPE_CBuffWindow__PostDraw)DetourFunction((PBYTE)EQ_FUNCTION_CBuffWindow__PostDraw, (PBYTE)EQMACMQ_DETOUR_CBuffWindow__PostDraw);
	EQMACMQ_REAL_EQ_Character__CastSpell = (EQ_FUNCTION_TYPE_EQ_Character__CastSpell)DetourFunction((PBYTE)EQ_FUNCTION_EQ_Character__CastSpell, (PBYTE)EQMACMQ_DETOUR_EQ_Character__CastSpell);
	heqwMod = GetModuleHandle("eqw.dll");
	LegalPlayerRace_Trampoline = (EQ_FUNCTION_TYPE_EQPlayer__LegalPlayerRace)DetourFunction((PBYTE)0x0050BD9D, (PBYTE)LegalPlayerRace_Detour);
	EQZoneInfo_Ctor_Trampoline = (EQ_FUNCTION_TYPE_EQZoneInfo__EQZoneInfo)DetourFunction((PBYTE)0x005223C6, (PBYTE)EQZoneInfo_Ctor_Detour);
	EQPlayer_GetActorTag_Trampoline = (EQ_FUNCTION_TYPE_EQPlayer_GetActorTag)DetourFunction((PBYTE)0x0050845D, (PBYTE)EQPlayer_GetActorTag_Detour);

	// Horse Support
	HasInvalidRiderTexture_Trampoline = (EQ_FUNCTION_TYPE_EQPlayer__HasInvalidRiderTexture)DetourFunction((PBYTE)0x0051FCA6, (PBYTE)HasInvalidRiderTexture_Detour);
	IsUntexturedHorse_Trampoline = (EQ_FUNCTION_TYPE_EQPlayer__HasInvalidRiderTexture)DetourFunction((PBYTE)0x0051FC6D, (PBYTE)IsUntexturedHorse_Detour);
	EQPlayer__MountEQPlayer_Trampoline = (EQ_FUNCTION_TYPE_EQPlayer__MountEQPlayer)DetourFunction((PBYTE)0x51FD83, (PBYTE)EQPlayer__MountEQPlayer_Detour);
	CEverquest__ProcessControls_Trampoline = (EQ_FUNCTION_TYPE_CEverquest__ProcessControls)DetourFunction((PBYTE)0x53F337, (PBYTE)CEverquest__ProcessControls_Detour);
	EQPlayer__AttachPlayerToDag_Trampoline = (EQ_FUNCTION_TYPE_EQPlayer__AttachPlayerToDag)DetourFunction((PBYTE)0x4B079F, (PBYTE)EQPlayer__AttachPlayerToDag_Detour);
	EQPlayer__Dismount_Trampoline = (EQ_FUNCTION_TYPE_EQPlayer__Dismount)DetourFunction((PBYTE)0x51FF5F, (PBYTE)EQPlayer__Dismount_Detour);
	DetourFunction((PBYTE)0x51FCE6, (PBYTE)IsHorse);
	

	// Sends DLL_VERSION to the server on zone-in
	OnZoneCallbacks.push_back(SendDllVersion_OnZone);
	CustomSpawnAppearanceMessageHandlers.push_back(HandleDllVersionRequest);

	// [BuffStackingPatch:Main]
	EQCharacter__FindAffectSlot_Trampoline = (EQ_FUNCTION_TYPE_EQCharacter__FindAffectSlot)DetourFunction((PBYTE)0x004C7A3E, (PBYTE)EQCharacter__FindAffectSlot_Detour);
	OnZoneCallbacks.push_back(BuffstackingPatch_OnZone);
	CustomSpawnAppearanceMessageHandlers.push_back(BuffstackingPatch_HandleHandshake);
	// [BuffStackingPacth:SongWindow]
	EQCharacter__GetBuff_Trampoline = (EQ_FUNCTION_TYPE_EQCharacter__GetBuff)DetourFunction((PBYTE)0x004C465A, (PBYTE)EQCharacter__GetBuff_Detour); // Supports reading buffs 16-30 in Song Window
	EQCharacter__GetMaxBuffs_Trampoline = (EQ_FUNCTION_TYPE_EQCharacter__GetMaxBuffs)DetourFunction((PBYTE)0x004C4637, (PBYTE)EQCHARACTER__GetMaxBuffs_Detour); // Uses 16+ buffs for buff loops (stat calcs etc)
	DetourFunction((PBYTE)0x00408FF1, (PBYTE)CBuffWindow__WndNotification_Detour); // Handles clicking off buffs 16+ on song window
	ApplySongWindowBytePatches(); // Fixes OP_Buff to work on all 30 slots
	InitGameUICallbacks.push_back(ShortBuffWindow_InitUI); // Loads Song window
	ActivateUICallbacks.push_back(ShowBuffWindow_ActivateUI);
	CleanUpUICallbacks.push_back(ShortBuffWindow_CleanUI);
	DeactivateUICallbacks.push_back(ShowBuffWindow_DeactivateUI);

	// Appearance / Tint Support
	SwapHead_Trampoline = (EQ_FUNCTION_TYPE_SwapHead)DetourFunction((PBYTE)0x4A1735, (PBYTE)SwapHead_Detour);
	SwapModel_Trampoline = (EQ_FUNCTION_TYPE_SwapModel)DetourFunction((PBYTE)0x4A9EB3, (PBYTE)SwapModel_Detour);
	WearChangeArmor_Trampoline = (EQ_FUNCTION_TYPE_WearChangeArmor)DetourFunction((PBYTE)0x4A2A7A, (PBYTE)WearChangeArmor_Detour);
	ApplyTintPatches();

	// Mesmerization Stun Duration fix
	ApplyMesmerizationFixes();

	return_ProcessMouseEvent = (ProcessGameEvents_t)DetourFunction((PBYTE)o_MouseEvents, (PBYTE)ProcessMouseEvent_Hook);
	//return_SetMouseCenter = (ProcessGameEvents_t)DetourFunction((PBYTE)o_MouseCenter, (PBYTE)SetMouseCenter_Hook);

	eqgfxMod = *(DWORD*)(0x007F9C50);
	d3ddev = (DWORD)(eqgfxMod + 0x00A4F92C);
		
	EzDetour(0x0055A4F4, WndProc_Detour, WndProc_Trampoline);
	// This detours key press down handler, so we can capture alt-enter to switch video modes
	EzDetour(EQ_FUNCTION_ProcessKeyDown, ProcessKeyDown_Detour, ProcessKeyDown_Trampoline);
	EzDetour(EQ_FUNCTION_ProcessKeyUp, ProcessKeyUp_Detour, ProcessKeyUp_Trampoline);
	
	EzDetour(EQ_FUNCTION_CEverQuest__RMouseDown, RightMouseDown_Detour, RightMouseDown_Trampoline);
	EzDetour(EQ_FUNCTION_CEverQuest__RMouseUp, RightMouseUp_Detour, RightMouseUp_Trampoline);
	EzDetour(EQ_FUNCTION_CEverQuest__LMouseDown, LeftMouseDown_Detour, LeftMouseDown_Trampoline);
	EzDetour(EQ_FUNCTION_CEverQuest__LMouseUp, LeftMouseUp_Detour, LeftMouseUp_Trampoline);
	EzDetour(0x004FA8C5, do_quit_Detour, do_quit_Trampoline);
	
	//EzDetour(0x00559BF4, GetCpuTicks2_Detour, GetCpuTicks2_Trampoline);

	EzDetour(0x00538CE6, CEverQuest__DisplayScreen_Detour, CEverQuest__DisplayScreen_Trampoline);

	// Add MGB for Beastlords
	EzDetour(0x004B8231, sub_4B8231_Detour, sub_4B8231_Trampoline);

	// Fix bug with Level of Detail setting always being turned on ignoring user's preference
	EzDetour(0x004A849E, &Eqmachooks::CDisplay__StartWorldDisplay_Detour, &Eqmachooks::CDisplay__StartWorldDisplay_Trampoline);

	// Fix bug with option window UI skin load dialog always loading default instead of selected skin
	uintptr_t addr = (intptr_t)sprintf_Detour_loadskin - (intptr_t)0x00426115;
	PatchA((void *)0x00426111, &addr, 4);

	// Fix bug with spell casting bar not showing at high spell haste values
	unsigned char jge = 0x7D;
	PatchA((void *)0x004c55b7, &jge, 1);

	//this one is here for eqplaynice - eqmule

	EzDetour(0x0055AFE2, &Eqmachooks::CDisplay__Process_Events_Detour, &Eqmachooks::CDisplay__Process_Events_Trampoline);

	EzDetour(EQ_FUNCTION_HandleMouseWheel, HandleMouseWheel_Detour, HandleMouseWheel_Trampoline);
	// for command line parsing
	EzDetour(0x004F35E5, sub_4F35E5_Detour, sub_4F35E5_Trampoline);

	EQMACMQ_REAL_CCharacterSelectWnd__Quit = (EQ_FUNCTION_TYPE_CCharacterSelectWnd__Quit)DetourFunction((PBYTE)EQ_FUNCTION_CCharacterSelectWnd__Quit, (PBYTE)EQMACMQ_DETOUR_CCharacterSelectWnd__Quit);

	EQMACMQ_REAL_CEverQuest__InterpretCmd = (EQ_FUNCTION_TYPE_CEverQuest__InterpretCmd)DetourFunction((PBYTE)EQ_FUNCTION_CEverQuest__InterpretCmd, (PBYTE)EQMACMQ_DETOUR_CEverQuest__InterpretCmd);

	char szResult[255];
	char szDefault[255];
	sprintf(szDefault, "%s", "TRUE");
	DWORD error = GetPrivateProfileStringA("Options", "WindowedMode", szDefault, szResult, 255, "./eqclient.ini");
	if (GetLastError())
	{
		WritePrivateProfileStringA_tramp("Options", "WindowedMode", szDefault, "./eqclient.ini");
	}
	if (!strcmp(szResult, "FALSE")) {
		start_fullscreen = true;
	}
	else {
		start_fullscreen = false;
	}

	sprintf(szDefault, "%d", 1);
	error = GetPrivateProfileStringA("Options", "MouseRightHanded", szDefault, szResult, 255, "./eqclient.ini");
	if (!GetLastError()) {
		if (!strcmp(szResult, "0"))
			RightHandMouse = false;
	}
	else {
		WritePrivateProfileStringA_tramp("Options", "MouseRightHanded", szDefault, "./eqclient.ini");
	}

	sprintf(szDefault, "%d", 32);
	error = GetPrivateProfileStringA("Defaults", "VideoModeBitsPerPixel", szDefault, szResult, 255, "./eqclient.ini");
	if (!GetLastError())
	{
		// if set to 16 bit, change to 32
		if (!strcmp(szResult, "16"))
			WritePrivateProfileStringA_tramp("Defaults", "VideoModeBitsPerPixel", szDefault, "./eqclient.ini");
	}
	
	sprintf(szDefault, "%d", 32);
	error = GetPrivateProfileStringA("VideoMode", "BitsPerPixel", szDefault, szResult, 255, "./eqclient.ini");
	if (!GetLastError())
	{
		// if set to 16 bit, change to 32
		if (!strcmp(szResult, "16"))
			WritePrivateProfileStringA_tramp("VideoMode", "BitsPerPixel", szDefault, "./eqclient.ini");
	}
	else {
		// we do not have one set
		DEVMODE dm;
		// initialize the DEVMODE structure
		ZeroMemory(&dm, sizeof(dm));
		dm.dmSize = sizeof(dm);
		DWORD bits = 32;
		DWORD freq = 40;
		if (0 != EnumDisplaySettings(NULL, ENUM_CURRENT_SETTINGS, &dm))
		{
			// get default display settings
			bits = dm.dmBitsPerPel;
			freq = dm.dmDisplayFrequency;
		}
		sprintf(szDefault, "%d", freq);
		WritePrivateProfileStringA_tramp("VideoMode", "RefreshRate", szDefault, "./eqclient.ini");
		sprintf(szDefault, "%d", bits);
		WritePrivateProfileStringA_tramp("VideoMode", "BitsPerPixel", szDefault, "./eqclient.ini");
	}

	// turn on chat keepalive
	sprintf(szDefault, "%d", 1);
	WritePrivateProfileStringA_tramp("Defaults", "ChatKeepAlive", szDefault, "./eqclient.ini");
	CheckClientMiniMods();
	InitRaceShortCodeMap();
	bInitalized=true;
}

void RemoveDetour(DWORD address)
{
	for(std::map<DWORD,_detourinfo>::iterator i = ourdetours.begin();i!=ourdetours.end();i++) {
		DetourRemove((PBYTE)i->second.tramp,(PBYTE)i->second.detour);
	}
}

void ExitHooks()
{
	if(!bInitalized)
	{
		return;
	}

	//RemoveDetour(0x4E829F); // HandleWorldMessage
	//RemoveDetour(0x4AA8BC); // RenderWorld
	//	RemoveDetour(gmfadress); // GetModuleFileNameA
	//RemoveDetour(wpsaddress); // WriteProfileStringA
	//RemoveDetour(0x4F2ED0); // SendExeChecksum
	//RemoveDetour(0x40F3E0);
	//RemoveDetour(cwAddress);
	//RemoveDetour(0x55AFE2); // ProcessEvents
	//RemoveDetour(EQ_FUNCTION_ProcessKeyDown); // process key down
	//RemoveDetour(EQ_FUNCTION_ProcessKeyUp); // process key up
	//RemoveDetour(EQ_FUNCTION_CEverQuest__RMouseDown);
	//RemoveDetour(EQ_FUNCTION_CEverQuest__RMouseUp);
	//RemoveDetour(EQ_FUNCTION_CEverQuest__LMouseDown);
	//RemoveDetour(EQ_FUNCTION_CEverQuest__LMouseUp);
	//RemoveDetour(0x55A4F4); // WndProc
	//RemoveDetour(0x538CE6); // DisplayScreen
	//RemoveDetour(0x4F35E5); // command line parsing
	//RemoveDetour(0x4B8231); // MGB for BST
	//RemoveDetour(0x4A849E); // LoD fix
	//RemoveDetour(0x4FA8C5); // do_quit
	//RemoveDetour(EQ_FUNCTION_HandleMouseWheel);

	//DetourRemove((PBYTE)EQMACMQ_REAL_CCharacterSelectWnd__Quit, (PBYTE)EQMACMQ_DETOUR_CCharacterSelectWnd__Quit);
	//DetourRemove((PBYTE)EQMACMQ_REAL_CBuffWindow__RefreshBuffDisplay, (PBYTE)EQMACMQ_DETOUR_CBuffWindow__RefreshBuffDisplay);
	//DetourRemove((PBYTE)EQMACMQ_REAL_CBuffWindow__PostDraw, (PBYTE)EQMACMQ_DETOUR_CBuffWindow__PostDraw);
	//DetourRemove((PBYTE)EQMACMQ_REAL_EQ_Character__CastSpell, (PBYTE)EQMACMQ_DETOUR_EQ_Character__CastSpell);
	//DetourRemove((PBYTE)EQMACMQ_REAL_CEverQuest__InterpretCmd, (PBYTE)EQMACMQ_DETOUR_CEverQuest__InterpretCmd);
}

BOOL APIENTRY DllMain( HANDLE hModule, DWORD  ul_reason_for_call, LPVOID lpReserved )
{
	if (ul_reason_for_call==DLL_PROCESS_ATTACH)
	{
		InitHooks();
		LoadIniSettings();
		SetEQhWnd();
		//CheckPromptUIChoice();
		return TRUE;
	}
	else if (ul_reason_for_call==DLL_PROCESS_DETACH) {
		ExitHooks();
	    return TRUE;
	}
}