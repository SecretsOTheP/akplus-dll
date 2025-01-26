//#include "..\zlib_x86\include\zlib.h"

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

// Custom Messaging Support
constexpr unsigned int SpawnAppearanceType_ClientDllMessage = 256;
void SendCustomSpawnAppearanceMessage(unsigned __int16 feature_id, unsigned __int16 feature_value, bool is_request);

// Song Window Support
struct _EQBUFFINFO* GetStartBuffArray(class CBuffWindow* window);
int GetStartBuffIndex(class CBuffWindow* window);
void SetTemporaryBuffOffset(int offset);

/*
voidpf eqemu_alloc_func(voidpf opaque, uInt items, uInt size);
void eqemu_free_func(voidpf opaque, voidpf address);



int DeflatePacket(const unsigned char* in_data, int in_length, unsigned char* out_data, int max_out_length);
unsigned int InflatePacket(const unsigned char* indata, unsigned int indatalen, unsigned char* outdata, unsigned int outdatalen, bool iQuiet = false);
*/
#endif
