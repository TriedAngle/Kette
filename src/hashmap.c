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

void hmInsert(HashMap* map, byte* key, i32 length, cell value) {
    if((map->count / map->size) >= map->increaseDelta100) {
        hmResize(map, map->size * map->expandFactor);
    }

    u64 index = hashFunction(key, length) % map->size;
    while(map->items[index].state == USED) {
        if(string_eq(map->items[index].key, map->items[index].length, key, length)) {
            break;
        }
        index = (index + 1) % map->size;
    }
    map->items[index].key = key;
    map->items[index].length = length;
    map->items[index].value = value;
    map->items[index].state = USED;
    map->count++;
}

cell hmGet(HashMap* map, byte* key, i32 length) {
    u64 index = hashFunction(key, length) % map->size;
    u64 startIndex = index;

    while(map->items[index].state != EMPTY) {
        if(map->items[index].state == USED &&
            string_eq(map->items[index].key, map->items[index].length, key, length)
        ) {
            return map->items[index].value;
        }

        index = (index + 1) % map->size;
        if (index == startIndex) {
            break;
        }
    }
    return -1;
}


cell hmDelete(HashMap* map, byte* key, i32 length) {
    u64 index = hashFunction(key, length) % map->size;
    u64 startIndex = index;

    while(map->items[index].state != EMPTY) {
        if(map->items[index].state == USED && 
            string_eq(map->items[index].key, map->items[index].length, key, length)
        ) {
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


void hmResize(HashMap* map, u32 newSize) {
    HashItem* old = map->items;
    u32 oldSize = map->size;

    map->items = (HashItem*) tcreate(&map->allocator, sizeof(HashItem) * newSize);
    map->size = newSize;
    map->count = 0;

    for (int i = 0; i < oldSize; i++) {
        if(old[i].state == USED) {
            hmInsert(map, old[i].key, old[i].length, old[i].value);
        }
    }

    tdelete(&map->allocator, (void*)old, sizeof(HashItem) * oldSize);
}

