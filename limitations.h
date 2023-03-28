#ifndef SIMPLICITY_LIMITATIONS_H
#define SIMPLICITY_LIMITATIONS_H

#define DAG_LEN_MAX 0x800000U
#define NUMBER_OF_TYPENAMES_MAX 0x1000U
#define CELLS_MAX 0x500000U /* 5120 Kibibits ought to be enough for anyone. */
_Static_assert(DAG_LEN_MAX <= SIZE_MAX , "DAG_LEN_MAX doesn't fit in size_t.");
_Static_assert(NUMBER_OF_TYPENAMES_MAX <= SIZE_MAX, "NUMBER_OF_TYPENAMES_MAX doesn't fit in size_t.");
_Static_assert(CELLS_MAX <= SIZE_MAX, "CELLS_MAX doesn't fit in size_t.");

#endif
