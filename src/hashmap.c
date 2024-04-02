#include "hashmap.h"

#define EMPTY 0
#define USED 1
#define DELETED 2

#define INCREASE_DELTA100 75
#define DECREASE_DELTA100 10
#define SIZE_MIN 16
#define EXPAND_FACTOR 2
#define SHRINK_FACTOR 2

// djb2 
u64 hashFunction(byte* str, i32 length) {
    u64 hash = 5381;
    for (size_t i = 0; i < length; ++i) {
        hash = ((hash << 5) + hash) + str[i];
    }
    return hash;
}

u64 hashByteArray(bytearray* ba) {
    return hashFunction(ba->data, ba->size);
}

u64 hashGeneric(cell value) {
    u64 hash;
    if(read_tag(value) == FIXNUM_TAG) {
        hash = hashFixnum(remove_tag(value));
    } else {
        bytearray* ba = (bytearray*)remove_tag(value); 
        hash = hashByteArray(ba);
    }
    return hash;
}

// no idea how good this is chatgpt gave me this
// TODO: benchmark this
u64 hashFixnum(cell val) {
    val = (~val) + (val << 21);
    val = val ^ (val >> 24);
    val = (val + (val << 3)) + (val << 8);
    val = val ^ (val >> 14);
    val = (val + (val << 2)) + (val << 4);
    val = val ^ (val >> 28);
    val = val + (val << 31);
    return val;
}

HashMap initHashMap(Allocator allocator, u32 size) {
    HashMap map;
    map.allocator = allocator;
    map.sizeMin = SIZE_MIN;
    map.increaseDelta100 = INCREASE_DELTA100;
    map.decreaseDelta100 = DECREASE_DELTA100;
    map.expandFactor = EXPAND_FACTOR;
    map.shrinkFactor = SHRINK_FACTOR;
    map.items = (HashItem*) tcreate(&map.allocator, size * sizeof(HashItem));
    map.size = size;
    map.count = 0;
    return map;
}

void deinitHashMap(HashMap* map) {
    tdelete(&map->allocator, (void*)map->items, map->size * sizeof(HashItem));
}

void hmResize(HashMap* map, u32 newSize) {
    HashItem* old = map->items;
    u32 oldSize = map->size;

    map->items = (HashItem*) tcreate(&map->allocator, sizeof(HashItem) * newSize);
    map->size = newSize;
    map->count = 0;

    for (int i = 0; i < oldSize; i++) {
        if(old[i].state == USED) {
            hmInsert(map, old[i].key, old[i].value);
        }
    }

    tdelete(&map->allocator, (void*)old, sizeof(HashItem) * oldSize);
}


void hmInsert(HashMap* map, cell key, cell value) {
    if((map->count / map->size) >= map->increaseDelta100) {
        hmResize(map, map->size * map->expandFactor);
    }

    u64 hash = hashGeneric(key);
    u64 index = hash % map->size;
    while(map->items[index].state == USED) {
        if(generic_eq(key, map->items[index].key)) {
            break;
        }
        index = (index + 1) % map->size;
    }
    map->items[index].key = key;
    map->items[index].value = value;
    map->items[index].state = USED;
    map->count++;
}

cell hmGet(HashMap* map, cell key) {
    u64 hash = hashGeneric(key);
    u64 index = hash % map->size;
    u64 startIndex = index;

    while(map->items[index].state != EMPTY) {
        if(map->items[index].state == USED && generic_eq(key, map->items[index].key)) {
            return map->items[index].value;
        }

        index = (index + 1) % map->size;
        if (index == startIndex) {
            break;
        }
    }
    return -1;
}


cell hmDelete(HashMap* map, cell key) {
    u64 hash = hashGeneric(key);
    u64 index = hash % map->size;
    u64 startIndex = index;

    while(map->items[index].state != EMPTY) {
        if(map->items[index].state == USED && generic_eq(key, map->items[index].key)) {
            map->items[index].state = DELETED;
            map->count--;
            cell value = map->items[index].value;

            if ((map->size > map->sizeMin) && (map->count / map->size < map->decreaseDelta100)) {
                hmResize(map, map->size / map->shrinkFactor);
            }
            return value;
        }
        index = (index + 1) % map->size;
        if (index == startIndex) {
            break;
        }
    }
    return -1;
}
