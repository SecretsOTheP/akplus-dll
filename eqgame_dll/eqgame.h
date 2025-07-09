//#include "..\zlib_x86\include\zlib.h"

#include <string>

#ifndef PACKET_FUNCTIONS_H
#define PACKET_FUNCTIONS_H


struct Merchant_DelItem_Struct
{
	/*000*/	unsigned short	npcid;			// Merchant NPC's entity id
	/*002*/	unsigned short	playerid;		// Player's entity id
	/*004*/	unsigned char	itemslot;       // Slot of the item you want to remove
	/*005*/	unsigned char	type;     // 0x40
							  /*006*/
};

struct SpawnAppearance_Struct { // sizeof=0x8
	/*000*/ unsigned short spawn_id;
	/*002*/ unsigned short type;
	/*004*/ unsigned int parameter;
	/*008*/
};

struct WearChange_Struct
{
	/*000*/ unsigned short spawn_id;
	/*002*/ unsigned char  wear_slot_id; // 0=Head 1=Chest 2=Arms 3=Wrist 4=Gloves 5=Legs 6=Boots 7=MH 8=OH
	/*003*/ unsigned char  align03;
	/*004*/ unsigned short material;     // Armor Material or IT### number in (Item->IDFile)
	/*006*/ unsigned short align06;
	/*008*/ unsigned int   color;
};

struct Illusion_Struct
{
	unsigned short spawnid;
	unsigned short race;
	unsigned char gender;
	unsigned char texture;
	unsigned char helmtexture;
	unsigned char unknown007; // maybe 16-bit helmtexture
	unsigned short face;
	unsigned char hairstyle;
	unsigned char haircolor;
	unsigned char beard;
	unsigned char beardcolor;
	unsigned short unknown_void;
	int size;
};

// Note: Normally this packet is just char_name[64], and extra data is NOT zero'd out.
// On Quarm we support custom values in this packet, starting from the end.
// If custom values are present, unknown00 is set to 0, and all padding bytes are zero'd out.
struct ClientZoneEntry_Struct
{
	/*0000*/	unsigned int	unknown00;      // Hash of first 32 bytes (zero if packet contains custom fields)
	/*0004*/	char	char_name[59];			// Character Name / Padding
	/*0063*/	char    buffstacking_support;   // [custom] The client support flag for the buffstacking modifications
	/*0064*/	char	song_window_slots;      // [custom] Number of song window slots the client can support
	/*0065*/	char	shared_bank;            // [custom] Number of shared bank slots the client can support
	/*0066*/	char	dll_version[2];         // [custom] Dll Version (uint16)
	/*0068*/
};

struct RaceData
{
	std::string actor_tag = "";
	std::string animation_fallback_tag = "";
};

struct BuffStackingInfo_Struct
{
	unsigned char buffstacking; // 0 = Legacy Stacking, 1 = New Buffstacking (V1)
	unsigned char song_window_slots;
	unsigned char standard_buff_slots; // Not used/supported. Just a placeholder if we ever support this
};

struct SharedBankInfo_Struct
{
	unsigned char mode;
	unsigned char bag_count; // Number of bag slots the client can deposit to
};

// Custom Race Support
RaceData* GetCustomRaceData(int race, int gender);
void PutCustomRaceData(int race, int gender, std::string actor_tag, std::string fallback_anim_actor_tag = "");

// Custom Messaging Support
constexpr unsigned int SpawnAppearanceType_ClientDllMessage = 256;
void SendCustomSpawnAppearanceMessage(unsigned __int16 feature_id, unsigned __int16 feature_value, bool is_request);

// Song Window Support
void Handle_OP_BuffStackingInfo(BuffStackingInfo_Struct* bsi);
__declspec(dllexport) class CShortBuffWindow* GetShortDurationBuffWindow();
struct _EQBUFFINFO* GetStartBuffArray(bool songs_buffs);
void MakeGetBuffReturnSongs(bool enabled);

// Tint Support
bool Handle_In_OP_WearChange(WearChange_Struct* wc);
bool Handle_Out_OP_WearChange(WearChange_Struct* wc);

// Horse Support
unsigned short GetActualHorseRaceID(struct _EQSPAWNINFO* entity);

// Bank Support
void Handle_OP_SharedBankInfo(SharedBankInfo_Struct* sbi);

/*
voidpf eqemu_alloc_func(voidpf opaque, uInt items, uInt size);
void eqemu_free_func(voidpf opaque, voidpf address);



int DeflatePacket(const unsigned char* in_data, int in_length, unsigned char* out_data, int max_out_length);
unsigned int InflatePacket(const unsigned char* indata, unsigned int indatalen, unsigned char* outdata, unsigned int outdatalen, bool iQuiet = false);
*/
#endif
