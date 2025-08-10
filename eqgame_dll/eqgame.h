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

struct Action_Struct
{
	/*00*/	unsigned short target;				// Target entity ID
	/*02*/	unsigned short	source;				// Caster entity ID
	/*04*/	unsigned short	level;				// this only does something for spell ids 1252-1266 (potions) and only accepts values 1-60, otherwise the action uses source entity level
	/*06*/	unsigned short	target_level;		// unused by client
	/*08*/	int	instrument_mod;		// normally 10, used for bard songs
	/*12*/	float	force;				// push force
	/*16*/	float	sequence;			// push heading
	/*20*/	float	pushup_angle;		// push pitch
	/*24*/	unsigned char type;				// 231 for spells
	/*25*/	unsigned char	unknown25;			// unused by client
	/*26*/	unsigned short	spell_id_unused;	// extra spell_id, not used by client
	/*28*/	short	tap_amount;			// used in client for instant, targettype 13 (tap) spells to set the amount that was tapped
	/*30*/	unsigned short	spell;				// spell_id
	/*32*/	unsigned char	unknown32;			// 0x00
	/*33*/  unsigned char	buff_unknown;		// 1 to start then 4 for success
	/*34*/	unsigned short	unknown34;			// unused by client
};

struct RaceData
{
	std::string actor_tag = "";
	std::string animation_fallback_tag = "";
};

// Custom Race Support
RaceData* GetCustomRaceData(int race, int gender);
void PutCustomRaceData(int race, int gender, std::string actor_tag, std::string fallback_anim_actor_tag = "");

// Custom Messaging Support
constexpr unsigned int SpawnAppearanceType_ClientDllMessage = 256;
void SendCustomSpawnAppearanceMessage(unsigned __int16 feature_id, unsigned __int16 feature_value, bool is_request);

// Song Window Support
__declspec(dllexport) class CShortBuffWindow* GetShortDurationBuffWindow();

// Tint Support
bool Handle_In_OP_WearChange(WearChange_Struct* wc);
bool Handle_Out_OP_WearChange(WearChange_Struct* wc);

// Horse Support
unsigned short GetActualHorseRaceID(struct _EQSPAWNINFO* entity);

struct _EQBUFFINFO* GetStartBuffArray(bool songs_buffs);
void MakeGetBuffReturnSongs(bool enabled);

/*
voidpf eqemu_alloc_func(voidpf opaque, uInt items, uInt size);
void eqemu_free_func(voidpf opaque, voidpf address);



int DeflatePacket(const unsigned char* in_data, int in_length, unsigned char* out_data, int max_out_length);
unsigned int InflatePacket(const unsigned char* indata, unsigned int indatalen, unsigned char* outdata, unsigned int outdatalen, bool iQuiet = false);
*/
#endif
