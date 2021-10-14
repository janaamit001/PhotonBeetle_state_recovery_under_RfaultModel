#ifdef _MSC_VER
#define _CRT_SECURE_NO_WARNINGS
#endif

#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <time.h>

#include "crypto_aead.h"
#include "photon.h"
#include "api.h"

#define KAT_SUCCESS          0
#define KAT_FILE_OPEN_ERROR -1
#define KAT_DATA_ERROR      -3
#define KAT_CRYPTO_FAILURE  -4

#define MAX_FILE_NAME				256
#define MAX_MESSAGE_LENGTH			32
#define MAX_ASSOCIATED_DATA_LENGTH	32
#define sboxSize 16

//const unsigned char WORDFILTER = 0xF;

extern uint8_t st[8][8], st1[8][8], st2[8][8], st3[8][8], st4[8][8], st5[8][8];
extern unsigned char ftag[ 16 ], nfstate[32], fstate[32];
unsigned char s[16] = {0xc, 0x5, 0x6, 0xb, 0x9, 0x0, 0xa, 0xd, 0x3, 0xe, 0xf, 0x8, 0x4, 0x7, 0x1, 0x2};

void init_buffer(unsigned char *buffer, unsigned long long numbytes);

void fprint_bstr(FILE *fp, const char *label, const unsigned char *data, unsigned long long length);

int generate_test_vectors();

int main()
{
	int ret = generate_test_vectors();

	if (ret != KAT_SUCCESS) {
		fprintf(stderr, "test vector generation failed with code %d\n", ret);
	}

	return ret;
}


/*unsigned char FieldMult(unsigned char a, unsigned char b)
{
	const unsigned char ReductionPoly = 0x3;
	unsigned char x = a, ret = 0;
	int i;
	for(i = 0; i < 4; i++) {
		if((b>>i)&1) ret ^= x;
		if(x&0x8) {
			x <<= 1;
			x ^= ReductionPoly;
		}
		else x <<= 1;
	}
	return ret&WORDFILTER;
}*/


void print( unsigned char *m ) {

	printf("Ciphertext::\n");
	for( short i = 0; i < 32; ++i )
		printf("%x ", m[ i ]);
		
	printf("\n\n");
	
	printf("Tag::\n");
	for( short i = 32; i < 48; ++i )
		printf("%02x ", m[ i ]);
		
	printf("\n\n");

	return;
}


void copy_ciphertext( unsigned char ct1[], unsigned char ct[] ) {

	for( short i = 0; i < 48; ++i )
		ct1[ i ] = ct[ i ];

	return;
}

void xor_of_diff_tag( uint8_t state[8][8], unsigned char ct1[] ) {

	uint8_t byte[ 16 ];
	short i, j, counter = 0;
	
	for( i = 0; i < 4; ++i ) {
	
		for( j = 0; j < 4; ++j ) {
		
			//byte[ counter ] = (( state[ i ][ j ] << 4 ) & 0xf0 ) ^ ( state[ i ][ j + 1 ] & 0x0f );
			byte[i*4+j]  = state[i][j*2  ] << 4;
			byte[i*4+j] |= state[i][j*2+1];
		}
	}
	
	counter = 0;
	for( i = 32; i < 48; ++i ) {
	
		ct1[ i ] ^= byte[ counter ];
		++counter;
	}

	return;
}


void print_state( unsigned char state[8][8] ) {

	for( short i = 0; i < 8; ++i ) {
	
		for( short j = 0; j < 8; ++j ) 
			printf("%x ", state[ i ][ j ] );
		
		printf("\n");
	}
	
	printf("\n");

	return;
}

void printDDT( unsigned char **ptr ) {


	for( int i = 0; i < 16; ++i ) {

		for( int j = 0; j < 16; ++j ) {

			printf("%d ", ptr[ i ][ j ]);
		}
		printf("\n");
	}

	return;
}


unsigned char **diffDistribution(unsigned char s[sboxSize]) {

	int i; 
	int x, y, delta, delta1;
	
	unsigned char** count = malloc(sboxSize*sizeof(int *));
	
	for(i = 0; i < sboxSize; ++i) {
		
		count[i] = malloc(sboxSize*sizeof(int));
		memset(count[i],0,sboxSize*sizeof(int));
	}
		
	for(y = 0; y < sboxSize; ++y) {
		
		for(x = 0; x < sboxSize; ++x) {
			
			delta = y^x;
			delta1 = s[x]^s[y];
			count[delta][delta1]++;
		}		
	}
	
	return count;
}


void Recover_state_columnwise( unsigned char pos, unsigned char count, unsigned char **ptr ) {

	unsigned char nfst[ 8 ][ 8 ], fst[ 8 ][ 8 ], temp[ 8 ][ 8 ], col[ 8 ][ 8 ];
	FILE *f0, *f1, *f2, *f3, *f4, *f5, *f6, *f7;
	unsigned char diff[ 8 ], diff1[ 8 ], delta, filename[ 24 ];
	unsigned char i, j;
	time_t t;

	srand( (unsigned) time( &t ) );
	

	/*for (i = 0; i < 16; ++i) {
	
		if( i%2 ) {
		
			nfst[i/4][i%4] = tag[i>>1] & 0xF;
			fst[i/4][i%4] = ftag[i>>1] & 0xF;
		}
		else {
		
			nfst[i/4][i%4] = (tag[i>>1] >> 4) & 0xF;
			fst[i/4][i%4] = (ftag[i>>1] >> 4) & 0xF;
		}
	}*/
	
	for (i = 0; i < 64; i++)
	{
		nfst[i / 8][i % 8] = (nfstate[i / 2] >> (4 * ((i & 1)^1))) & 0xf;
		fst[i / 8][i % 8] = (fstate[i / 2] >> (4 * ((i & 1)^1))) & 0xf;
	}
	
	for( i = 0; i < 8; ++i ) {
	
		for( j = 0; j < 8; ++j ) 
			temp[ i ][ j ] = nfst[ i ][ j ] ^ fst[ i ][ j ];
	}
	
	
	
	
	//print_state(nfst);
	//print_state(fst);
	
	//print_state(temp);
	printf("Full state difference::\n");
	for( short i = 0; i < 8; ++i ) {
	
		for( short j = 0; j < 8; ++j ) 
			printf("%x ", temp[ i ][ j ] );
		
		printf("\n");
	}
	
	printf("\n");
	
	invMixColumn( temp );
	//print_state( temp );
	invShiftRow( temp );
	//print_state( temp );
	
	printf("Full state difference::\n");
	for( short i = 0; i < 8; ++i ) {
	
		for( short j = 0; j < 8; ++j ) 
			printf("%x ", temp[ i ][ j ] );
		
		printf("\n");
	}
	
	printf("\n");
	
	printf("Right hand diff:\n");
	for( i = 0; i < 8; ++i ) {
	
		diff[ i ] = temp[ i ][ pos ];
		printf("%x ", diff[ i ]);
	}
		
	printf("\n");
		
	sprintf(filename, "key_column%d%d0.txt", pos, count);
	if ((f0 = fopen(filename, "w")) == NULL) {
		fprintf(stderr, "Couldn't open <%s> for write\n", filename);
		exit(1);
	}
	
	sprintf(filename, "key_column%d%d1.txt", pos, count);
	if ((f1 = fopen(filename, "w")) == NULL) {
		fprintf(stderr, "Couldn't open <%s> for write\n", filename);
		exit(1);
	}
	
	sprintf(filename, "key_column%d%d2.txt", pos, count);
	if ((f2 = fopen(filename, "w")) == NULL) {
		fprintf(stderr, "Couldn't open <%s> for write\n", filename);
		exit(1);
	}
	
	sprintf(filename, "key_column%d%d3.txt", pos, count);
	if ((f3 = fopen(filename, "w")) == NULL) {
		fprintf(stderr, "Couldn't open <%s> for write\n", filename);
		exit(1);
	}
	
	
	/**********************************/
	sprintf(filename, "key_column%d%d4.txt", pos, count);
	if ((f4 = fopen(filename, "w")) == NULL) {
		fprintf(stderr, "Couldn't open <%s> for write\n", filename);
		exit(1);
	}
	
	sprintf(filename, "key_column%d%d5.txt", pos, count);
	if ((f5 = fopen(filename, "w")) == NULL) {
		fprintf(stderr, "Couldn't open <%s> for write\n", filename);
		exit(1);
	}
	
	sprintf(filename, "key_column%d%d6.txt", pos, count);
	if ((f6 = fopen(filename, "w")) == NULL) {
		fprintf(stderr, "Couldn't open <%s> for write\n", filename);
		exit(1);
	}
	
	sprintf(filename, "key_column%d%d7.txt", pos, count);
	if ((f7 = fopen(filename, "w")) == NULL) {
		fprintf(stderr, "Couldn't open <%s> for write\n", filename);
		exit(1);
	}
	
	//printf("diff[100] = %x\n", diff[100]);
	i = 0;
	while( 1 ) {

	//for( i = 0; i < 16; ++i ) {
	
		delta = rand() & 0xf;
		diff1[ 0 ] = FieldMult( 0x2, delta );
		diff1[ 1 ] = FieldMult( 0xc, delta );
		diff1[ 2 ] = FieldMult( 0x4, delta );
		diff1[ 3 ] = FieldMult( 0x1, delta );
		
		diff1[ 4 ] = FieldMult( 0xf, delta );
		diff1[ 5 ] = FieldMult( 0x9, delta );
		diff1[ 6 ] = FieldMult( 0xc, delta );
		diff1[ 7 ] = FieldMult( 0xf, delta );

		printf("i = %d, check!!!\n", i);
		
		if( ( ptr[diff1[0]][diff[0]] > 0 ) && ( ptr[diff1[1]][diff[1]] > 0 ) && ( ptr[diff1[2]][diff[2]] > 0 ) && ( ptr[diff1[3]][diff[3]] > 0 ) && ( ptr[diff1[4]][diff[4]] > 0 ) && ( ptr[diff1[5]][diff[5]] > 0 ) && ( ptr[diff1[6]][diff[6]] > 0 ) && ( ptr[diff1[7]][diff[7]] > 0 )) {
		
			printf("..........delta = %x\n", delta);
			printf("Left hand diff:\n");
			for( j = 0; j < 8; ++j )
				printf("%x ", diff1[ j ]);
			printf("\n");
			break;
			//i = 15;
		}
		++i;
	}	
	
	printf("%x, %x, %x, %x, %x, %x, %x, %x,\t\t %x, %x, %x, %x, %x, %x, %x, %x\n", diff[0], diff[1], diff[2], diff[3], diff[4], diff[5], diff[6], diff[7], diff1[0], diff1[1], diff1[2], diff1[3], diff1[4], diff1[5], diff1[6], diff1[7]);
	for( i = 0; i < 16; ++i ) {
	
		
		//printf("0-> %x %x %x\n", i, s[ i ] ^ s[ i ^ diff1[ 0 ] ], diff[ 0 ]);
		if( ( s[ i ] ^ s[ i ^ diff1[ 0 ] ] ) == diff[ 0 ] ) {
			
			printf("f0:: i = %x, diff = %x\n", i, diff[ 0 ]);
			fprint_bstr(f0, "", &i, 1);
		}
		
		//printf("1-> %x %x %x\n", i, s[ i ] ^ s[ i ^ diff1[ 1 ] ], diff[ 1 ]);		
		if( ( s[ i ] ^ s[ i ^ diff1[ 1 ] ] ) == diff[ 1 ] ) {
			
			printf("f1:: i = %x, diff = %x\n", i, diff[ 1 ]);
			fprint_bstr(f1, "", &i, 1);
		}
		
		//printf("2-> %x %x %x\n", i, s[ i ] ^ s[ i ^ diff1[ 2 ] ], diff[ 2 ]);		
		if( ( s[ i ] ^ s[ i ^ diff1[ 2 ] ] ) == diff[ 2 ] ) {
			
			printf("f2:: i = %x, diff = %x\n", i, diff[ 2 ]);
			fprint_bstr(f2, "", &i, 1);
		}
		
		//printf("3-> %x %x %x\n", i, s[ i ] ^ s[ i ^ diff1[ 3 ] ], diff[ 3 ]);		
		if( ( s[ i ] ^ s[ i ^ diff1[ 3 ] ] ) == diff[ 3 ] ) {
			
			printf("f3:: i = %x, diff = %x\n", i, diff[ 3 ]);
			fprint_bstr(f3, "", &i, 1);
		}
		
		//printf("0-> %x %x %x\n", i, s[ i ] ^ s[ i ^ diff1[ 0 ] ], diff[ 0 ]);
		if( ( s[ i ] ^ s[ i ^ diff1[ 4 ] ] ) == diff[ 4 ] ) {
			
			printf("f4:: i = %x, diff = %x\n", i, diff[ 4 ]);
			fprint_bstr(f4, "", &i, 1);
		}
		
		//printf("1-> %x %x %x\n", i, s[ i ] ^ s[ i ^ diff1[ 1 ] ], diff[ 1 ]);		
		if( ( s[ i ] ^ s[ i ^ diff1[ 5 ] ] ) == diff[ 5 ] ) {
			
			printf("f5:: i = %x, diff = %x\n", i, diff[ 5 ]);
			fprint_bstr(f5, "", &i, 1);
		}
		
		//printf("2-> %x %x %x\n", i, s[ i ] ^ s[ i ^ diff1[ 2 ] ], diff[ 2 ]);		
		if( ( s[ i ] ^ s[ i ^ diff1[ 6 ] ] ) == diff[ 6 ] ) {
			
			printf("f6:: i = %x, diff = %x\n", i, diff[ 6 ]);
			fprint_bstr(f6, "", &i, 1);
		}
		
		//printf("3-> %x %x %x\n", i, s[ i ] ^ s[ i ^ diff1[ 3 ] ], diff[ 3 ]);		
		if( ( s[ i ] ^ s[ i ^ diff1[ 7 ] ] ) == diff[ 7 ] ) {
			
			printf("f7:: i = %x, diff = %x\n", i, diff[ 7 ]);
			fprint_bstr(f7, "", &i, 1);
		}
	}
	
	fclose( f0 );
	fclose( f1 );
	fclose( f2 );
	fclose( f3 );
	fclose( f4 );
	fclose( f5 );
	fclose( f6 );
	fclose( f7 );
		
	printf("\n***************************************************\n");
	return;
}


unsigned short findMax( unsigned short arr[] ) {

	unsigned short max = 0;

	for( unsigned char i = 0; i < 16; ++i ) {
	
		if( max < arr[ i ] )
			max = arr[ i ];
	}

	return( max );
}


void state_column0( ) {

	FILE *fp1; 
	unsigned char val;
	unsigned short max, arr[ 16 ] = {0};
	unsigned short num = 0, count1 = 0;
	unsigned char filename[ 24 ];

	int number = 8;
	printf("First Column::\n");
	
	for( unsigned char col= 0; col < 8; ++col ) {
	
		for( unsigned char count = 0; count < number; ++count ) {
		
			sprintf(filename, "key_column0%d%d.txt", count, col);
			if ((fp1 = fopen(filename, "r+")) == NULL) {
				fprintf(stderr, "Couldn't open <%s> for read\n", filename);
				exit(1);
			}
			fseek(fp1, 0, SEEK_SET);
			while(fread(&val, 1, 1, fp1) == 1) {
			

				//printf ("val = %c", val);
				if( ( val == 'a' ) || ( val == 'b' ) || ( val == 'c' ) || ( val == 'd' ) || ( val == 'e' ) || ( val == 'f' ) )
					val = val - 97 + 10;
				else 
					val = val - 48;
					
				//printf ("......val = %x\n", val);
				
				arr[ val ] += 1;
			}
			//printf("\n");
			fclose( fp1 );
		}

		printf("{ ");

		max = findMax( arr );
		printf("max = %d:: ", max);
		for( unsigned char i = 0; i < 16; ++i ) {
	
			if( arr[ i ] == max ) {
			
				printf("%x ", i );
				//printf("1st column = %04x\n", i);
				//++count1;
			}
		}
		printf("}");
		//printf("\n............\n");
		for( unsigned char i = 0; i < 16; ++i )
			arr[ i ] = 0;	
	}
	printf("\n");
}


void state_column1( ) {

	FILE *fp1; 
	unsigned char val;
	unsigned short max, arr[ 16 ] = {0};
	unsigned short num = 0, count1 = 0;
	unsigned char filename[ 24 ];

	int number = 8;
	printf("Second Column::\n");
	
	for( unsigned char col= 0; col < 8; ++col ) {
	
		for( unsigned char count = 0; count < number; ++count ) {
		
			sprintf(filename, "key_column1%d%d.txt", count, col);
			if ((fp1 = fopen(filename, "r+")) == NULL) {
				fprintf(stderr, "Couldn't open <%s> for read\n", filename);
				exit(1);
			}
			fseek(fp1, 0, SEEK_SET);
			while(fread(&val, 1, 1, fp1) == 1) {
			

				//printf ("val = %c", val);
				if( ( val == 'a' ) || ( val == 'b' ) || ( val == 'c' ) || ( val == 'd' ) || ( val == 'e' ) || ( val == 'f' ) )
					val = val - 97 + 10;
				else 
					val = val - 48;
					
				//printf ("......val = %x\n", val);
				
				arr[ val ] += 1;
			}
			//printf("\n");
			fclose( fp1 );
		}

		printf("{ ");

		max = findMax( arr );
		printf("max = %d:: ", max);
		for( unsigned char i = 0; i < 16; ++i ) {
	
			if( arr[ i ] == max ) {
			
				printf("%x ", i );
				//printf("1st column = %04x\n", i);
				//++count1;
			}
		}
		printf("}");
		//printf("\n............\n");
		for( unsigned char i = 0; i < 16; ++i )
			arr[ i ] = 0;	
	}
	printf("\n");
}


void state_column2( ) {

	FILE *fp1; 
	unsigned char val;
	unsigned short max, arr[ 16 ] = {0};
	unsigned short num = 0, count1 = 0;
	unsigned char filename[ 24 ];

	int number = 8;
	printf("Third Column::\n");
	
	for( unsigned char col= 0; col < 8; ++col ) {
	
		for( unsigned char count = 0; count < number; ++count ) {
		
			sprintf(filename, "key_column2%d%d.txt", count, col);
			if ((fp1 = fopen(filename, "r+")) == NULL) {
				fprintf(stderr, "Couldn't open <%s> for read\n", filename);
				exit(1);
			}
			fseek(fp1, 0, SEEK_SET);
			while(fread(&val, 1, 1, fp1) == 1) {
			

				//printf ("val = %c", val);
				if( ( val == 'a' ) || ( val == 'b' ) || ( val == 'c' ) || ( val == 'd' ) || ( val == 'e' ) || ( val == 'f' ) )
					val = val - 97 + 10;
				else 
					val = val - 48;
					
				//printf ("......val = %x\n", val);
				
				arr[ val ] += 1;
			}
			//printf("\n");
			fclose( fp1 );
		}

		printf("{ ");

		max = findMax( arr );
		printf("max = %d:: ", max);
		for( unsigned char i = 0; i < 16; ++i ) {
	
			if( arr[ i ] == max ) {
			
				printf("%x ", i );
				//printf("1st column = %04x\n", i);
				//++count1;
			}
		}
		printf("}");
		//printf("\n............\n");
		for( unsigned char i = 0; i < 16; ++i )
			arr[ i ] = 0;	
	}
	printf("\n");
}


void state_column3( ) {

	FILE *fp1; 
	unsigned char val;
	unsigned short max, arr[ 16 ] = {0};
	unsigned short num = 0, count1 = 0;
	unsigned char filename[ 24 ];

	int number = 8;
	printf("Fourth Column::\n");
	
	for( unsigned char col= 0; col < 8; ++col ) {
	
		for( unsigned char count = 0; count < number; ++count ) {
		
			sprintf(filename, "key_column3%d%d.txt", count, col);
			if ((fp1 = fopen(filename, "r+")) == NULL) {
				fprintf(stderr, "Couldn't open <%s> for read\n", filename);
				exit(1);
			}
			fseek(fp1, 0, SEEK_SET);
			while(fread(&val, 1, 1, fp1) == 1) {
			

				//printf ("val = %c", val);
				if( ( val == 'a' ) || ( val == 'b' ) || ( val == 'c' ) || ( val == 'd' ) || ( val == 'e' ) || ( val == 'f' ) )
					val = val - 97 + 10;
				else 
					val = val - 48;
					
				//printf ("......val = %x\n", val);
				
				arr[ val ] += 1;
			}
			//printf("\n");
			fclose( fp1 );
		}

		printf("{ ");

		max = findMax( arr );
		printf("max = %d:: ", max);
		for( unsigned char i = 0; i < 16; ++i ) {
	
			if( arr[ i ] == max ) {
			
				printf("%x ", i );
				//printf("1st column = %04x\n", i);
				//++count1;
			}
		}
		printf("}");
		//printf("\n............\n");
		for( unsigned char i = 0; i < 16; ++i )
			arr[ i ] = 0;	
	}
	printf("\n");
}


void state_column4( ) {

	FILE *fp1; 
	unsigned char val;
	unsigned short max, arr[ 16 ] = {0};
	unsigned short num = 0, count1 = 0;
	unsigned char filename[ 24 ];

	int number = 8;
	printf("Fifth Column::\n");
	
	for( unsigned char col= 0; col < 8; ++col ) {
	
		for( unsigned char count = 0; count < number; ++count ) {
		
			sprintf(filename, "key_column4%d%d.txt", count, col);
			if ((fp1 = fopen(filename, "r+")) == NULL) {
				fprintf(stderr, "Couldn't open <%s> for read\n", filename);
				exit(1);
			}
			fseek(fp1, 0, SEEK_SET);
			while(fread(&val, 1, 1, fp1) == 1) {
			

				//printf ("val = %c", val);
				if( ( val == 'a' ) || ( val == 'b' ) || ( val == 'c' ) || ( val == 'd' ) || ( val == 'e' ) || ( val == 'f' ) )
					val = val - 97 + 10;
				else 
					val = val - 48;
					
				//printf ("......val = %x\n", val);
				
				arr[ val ] += 1;
			}
			//printf("\n");
			fclose( fp1 );
		}

		printf("{ ");

		max = findMax( arr );
		printf("max = %d:: ", max);
		for( unsigned char i = 0; i < 16; ++i ) {
	
			if( arr[ i ] == max ) {
			
				printf("%x ", i );
				//printf("1st column = %04x\n", i);
				//++count1;
			}
		}
		printf("}");
		//printf("\n............\n");
		for( unsigned char i = 0; i < 16; ++i )
			arr[ i ] = 0;	
	}
	printf("\n");
}

void state_column5( ) {

	FILE *fp1; 
	unsigned char val;
	unsigned short max, arr[ 16 ] = {0};
	unsigned short num = 0, count1 = 0;
	unsigned char filename[ 24 ];

	int number = 8;
	printf("Sixth Column::\n");
	
	for( unsigned char col= 0; col < 8; ++col ) {
	
		for( unsigned char count = 0; count < number; ++count ) {
		
			sprintf(filename, "key_column5%d%d.txt", count, col);
			if ((fp1 = fopen(filename, "r+")) == NULL) {
				fprintf(stderr, "Couldn't open <%s> for read\n", filename);
				exit(1);
			}
			fseek(fp1, 0, SEEK_SET);
			while(fread(&val, 1, 1, fp1) == 1) {
			

				//printf ("val = %c", val);
				if( ( val == 'a' ) || ( val == 'b' ) || ( val == 'c' ) || ( val == 'd' ) || ( val == 'e' ) || ( val == 'f' ) )
					val = val - 97 + 10;
				else 
					val = val - 48;
					
				//printf ("......val = %x\n", val);
				
				arr[ val ] += 1;
			}
			//printf("\n");
			fclose( fp1 );
		}

		printf("{ ");

		max = findMax( arr );
		printf("max = %d:: ", max);
		for( unsigned char i = 0; i < 16; ++i ) {
	
			if( arr[ i ] == max ) {
			
				printf("%x ", i );
				//printf("1st column = %04x\n", i);
				//++count1;
			}
		}
		printf("}");
		//printf("\n............\n");
		for( unsigned char i = 0; i < 16; ++i )
			arr[ i ] = 0;	
	}
	printf("\n");
}

void state_column6( ) {

	FILE *fp1; 
	unsigned char val;
	unsigned short max, arr[ 16 ] = {0};
	unsigned short num = 0, count1 = 0;
	unsigned char filename[ 24 ];

	int number = 8;
	printf("Seventh Column::\n");
	
	for( unsigned char col= 0; col < 8; ++col ) {
	
		for( unsigned char count = 0; count < number; ++count ) {
		
			sprintf(filename, "key_column6%d%d.txt", count, col);
			if ((fp1 = fopen(filename, "r+")) == NULL) {
				fprintf(stderr, "Couldn't open <%s> for read\n", filename);
				exit(1);
			}
			fseek(fp1, 0, SEEK_SET);
			while(fread(&val, 1, 1, fp1) == 1) {
			

				//printf ("val = %c", val);
				if( ( val == 'a' ) || ( val == 'b' ) || ( val == 'c' ) || ( val == 'd' ) || ( val == 'e' ) || ( val == 'f' ) )
					val = val - 97 + 10;
				else 
					val = val - 48;
					
				//printf ("......val = %x\n", val);
				
				arr[ val ] += 1;
			}
			//printf("\n");
			fclose( fp1 );
		}

		printf("{ ");

		max = findMax( arr );
		printf("max = %d:: ", max);
		for( unsigned char i = 0; i < 16; ++i ) {
	
			if( arr[ i ] == max ) {
			
				printf("%x ", i );
				//printf("1st column = %04x\n", i);
				//++count1;
			}
		}
		printf("}");
		//printf("\n............\n");
		for( unsigned char i = 0; i < 16; ++i )
			arr[ i ] = 0;	
	}
	printf("\n");
}


void state_column7( ) {

	FILE *fp1; 
	unsigned char val;
	unsigned short max, arr[ 16 ] = {0};
	unsigned short num = 0, count1 = 0;
	unsigned char filename[ 24 ];

	int number = 8;
	printf("Eighth Column::\n");
	
	for( unsigned char col= 0; col < 8; ++col ) {
	
		for( unsigned char count = 0; count < number; ++count ) {
		
			sprintf(filename, "key_column7%d%d.txt", count, col);
			if ((fp1 = fopen(filename, "r+")) == NULL) {
				fprintf(stderr, "Couldn't open <%s> for read\n", filename);
				exit(1);
			}
			fseek(fp1, 0, SEEK_SET);
			while(fread(&val, 1, 1, fp1) == 1) {
			

				//printf ("val = %c", val);
				if( ( val == 'a' ) || ( val == 'b' ) || ( val == 'c' ) || ( val == 'd' ) || ( val == 'e' ) || ( val == 'f' ) )
					val = val - 97 + 10;
				else 
					val = val - 48;
					
				//printf ("......val = %x\n", val);
				
				arr[ val ] += 1;
			}
			//printf("\n");
			fclose( fp1 );
		}

		printf("{ ");

		max = findMax( arr );
		printf("max = %d:: ", max);
		for( unsigned char i = 0; i < 16; ++i ) {
	
			if( arr[ i ] == max ) {
			
				printf("%x ", i );
				//printf("1st column = %04x\n", i);
				//++count1;
			}
		}
		printf("}");
		//printf("\n............\n");
		for( unsigned char i = 0; i < 16; ++i )
			arr[ i ] = 0;	
	}
	printf("\n");
}










int generate_test_vectors()
{
	FILE                *fp;
	char                fileName[MAX_FILE_NAME];
	unsigned char       key[CRYPTO_KEYBYTES] = {0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0xf1};
	unsigned char		nonce[CRYPTO_NPUBBYTES];// = {0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0xf1};
	unsigned char       msg[MAX_MESSAGE_LENGTH];// = {0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0xf1};
	unsigned char       msg2[MAX_MESSAGE_LENGTH];
	unsigned char		ad[MAX_ASSOCIATED_DATA_LENGTH];// = {0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0xf1};
	unsigned char		ct[MAX_MESSAGE_LENGTH + CRYPTO_ABYTES], ct1[MAX_MESSAGE_LENGTH + CRYPTO_ABYTES];
	//unsigned long long  clen, mlen2;
	//int                 count = 1;
	int                 func_ret, ret_val = KAT_SUCCESS;
	
	unsigned long long mlen, mlen2, clen, adlen;
	unsigned char diff, diff1, diff2, diff3, diff4, diff5, diff6, diff7, diff8;
	uint8_t state[ 8 ][ 8 ], dstate[8][8];
	unsigned char tag[ 16 ];
	unsigned char count = 0, pos = 0;
	unsigned char **ddt = diffDistribution(s);
	int i, j;
	
	
	time_t t;
	srand( (unsigned) time( &t ) );

	//init_buffer(key, sizeof(key));
	init_buffer(nonce, sizeof(nonce));
	init_buffer(msg, sizeof(msg));
	init_buffer(ad, sizeof(ad));
	
	mlen = adlen = mlen2 = 32;
	clen = 48;
	
	printDDT( &ddt[ 0 ] );
	
	printf("...............Encryption.....................\n");
	if ( crypto_aead_encrypt(ct, &clen, msg, mlen, ad, adlen, NULL, nonce, key) == 0)
		print(ct);
		
	for( i = 32; i < 48; ++i )
		tag[i-32] = ct[i];
		
	if ( crypto_aead_decrypt(msg2, &mlen2, NULL, ct, clen, ad, adlen, nonce, key) == 0) {
	
		print(ct);
		printf("Decryption is successful!!\n\n\n");
	}
	else
		printf("Not successful!!\n\n\n");
		
		
		
		
	for( pos = 0; pos < 8; ++pos ) {
	
		printf("faulty forgery by injecting fault at the nibble position (0,%d)\n\n", pos);	
		for( unsigned char i1 = 0; i1 < 16; ++i1 ) {
		
			for( unsigned char i2 = 0; i2 < 16; ++i2 ) {
		
				for( unsigned char i3 = 0; i3 < 16; ++i3 ) {
		
					for( unsigned char i4 = 0; i4 < 16; ++i4 ) {
					
						for( unsigned char i5 = 0; i5 < 16; ++i5 ) {
		
							for( unsigned char i6 = 0; i6 < 16; ++i6 ) {
		
								for( unsigned char i7 = 0; i7 < 16; ++i7 ) {
		
									for( unsigned char i8 = 0; i8 < 16; ++i8 ) {

						
						
										for( i = 0; i < 8; ++i ) {
						
											for( j = 0; j < 8; ++j )
												state[ i ][ j ] = 0;
										}
										
										diff1 = rand() & 0xf;
										if( diff1 == 0 )
											diff1 = rand() & 0xf;
										state[ 0 ][ pos ] = diff1;
										
										diff2 = rand() & 0xf;
										if( diff2 == 0 )
											diff2 = rand() & 0xf;
										state[ 1 ][ pos ] = diff2;
										
										diff3 = rand() & 0xf;
										if( diff3 == 0 )
											diff3 = rand() & 0xf;
										state[ 2 ][ pos ] = diff3;
										
										diff4 = rand() & 0xf;
										if( diff4 == 0 )
											diff4 = rand() & 0xf;
										state[ 3 ][ pos ] = diff4;
										//next 4
										diff5 = rand() & 0xf;
										if( diff5 == 0 )
											diff5 = rand() & 0xf;
										state[ 4 ][ pos ] = diff5;
										
										diff6 = rand() & 0xf;
										if( diff6 == 0 )
											diff6 = rand() & 0xf;
										state[ 5 ][ pos ] = diff6;
										
										diff7 = rand() & 0xf;
										if( diff7 == 0 )
											diff7 = rand() & 0xf;
										state[ 6 ][ pos ] = diff7;
										
										diff8 = rand() & 0xf;
										if( diff8 == 0 )
											diff8 = rand() & 0xf;
										state[ 7 ][ pos ] = diff8;
										/*printf("state difference before sr and mc:\n");
										print_state( state );*/
										ShiftRow(state);
										MixColumn( state );
										//printf("state difference after sr and mc:\n");
										//print_state( state );
										copy_ciphertext( ct1, ct );
										xor_of_diff_tag( state, ct1 );
										
										//print(ct1);
										
										//for( i = 1; i< 16; ++i ) {
										
											//print(ct1);
											diff = rand() & 0xf;
											if( diff == 0 )
												diff = rand() & 0xf;
											//printf("fault in the dec query\n");	
											if ( fault_on_crypto_aead_decrypt(msg2, &mlen2, NULL, ct1, clen, ad, adlen, nonce, key, diff, pos ) == 0 ) {
												
												//printf("TAG DIFFERENCES:\n");
												//for( i = 32; i < 48; ++i ) 
												//	printf("%x, ", ct[i]^ct1[i]);
												
												
												//print(ct1);
												

												
												printf("\nTag Compare is successful!!Tag Compare is successful!!Tag Compare is successful!!Tag Compare is successful!!\n\n");
												//printf("idiff = %x, odiff = %x %x %x %x %x %x %x %x\n", diff, diff1, diff2, diff3, diff4, diff5, diff6, diff7, diff8);
												//extract_tags( ct, ct1, tag, ftag );
												//print_tags( tag, ftag );

												/*printf("\nkeys::\n");
												for( i = 0; i < 8; ++i ) {
												
													if( ( i != 0 ) && ( i % 2 == 0 ) )
														printf("\n");
													printf("%02x ", Rstate1[ i ]^tag[ i ]);
												}*/

												printf("enter into the fun::Recover_state_columnwise\n");
												//count = 4;
												Recover_state_columnwise( pos, count, &ddt[ 0 ] );
												//printf("............................................\n");
												//return 0;
												++count;
											}
											
										if(count == 4) break;
										}
									if(count == 4) break;
									}
								if(count == 4) break;
								}
							if(count == 4) break;
							}
						if(count == 4) break;
							
						}
					if(count == 4) break;
					}
									
				if(count == 4) break;	
				}
				
			if(count == 4) break;
			}
		}
			
	
	/*printf("faulty tag::\n");
	print(ct1);
	printf("Actual TAG DIFFERENCES:\n");
	for( i = 0; i < 16; ++i ) 
		printf("%x, ", ftag[i]^tag[i]);*/
		
	printf("\nActual state values after s-box\n");
	for( short i = 0; i < 8; ++i ) {
	
		for( short j = 0; j < 8; ++j ) {
		
			//dstate[i][j] = st[ i ][ j ]^st1[ i ][ j ];
			printf("%x ", st[ i ][ j ]);
		}
		
		printf("\n");
	}
	
	printf("\n");	
	
		
	/*printf("\nstate difference after last round s-box\n");
	for( short i = 0; i < 8; ++i ) {
	
		for( short j = 0; j < 8; ++j ) {
		
			dstate[i][j] = st[ i ][ j ]^st1[ i ][ j ];
			printf("%x ", dstate[ i ][ j ]);
		}
		
		printf("\n");
	}
	
	printf("\n");
	
	printf("\nstate difference after last round SR\n");
	for( short i = 0; i < 8; ++i ) {
	
		for( short j = 0; j < 8; ++j ) {
		
			//dstate[i][j] = st2[ i ][ j ]^st3[ i ][ j ];
			printf("%x ", st4[ i ][ j ]^st5[ i ][ j ]);
		}
		
		printf("\n");
	}
	
	printf("\n");
	
	printf("\nstate difference after last round MC\n");
	for( short i = 0; i < 8; ++i ) {
	
		for( short j = 0; j < 8; ++j ) {
		
			//dstate[i][j] = st2[ i ][ j ]^st3[ i ][ j ];
			printf("%x ", st2[ i ][ j ]^st3[ i ][ j ]);
		}
		
		printf("\n");
	}
	
	printf("\n");
	
	ShiftRow(dstate);
	printf("state difference after sr:\n");
	print_state( dstate );
	MixColumn( dstate );
	printf("state difference after mc:\n");
	print_state( dstate );*/
	
	
	state_column0();
	state_column1();
	state_column2();
	state_column3();
	state_column4();
	state_column5();
	state_column6();
	state_column7();
	
	return 0;
}


void fprint_bstr(FILE *fp, const char *label, const unsigned char *data, unsigned long long length)
{    
    //fprintf(fp, "%s", label);
        
	for (unsigned long long i = 0; i < length; i++)
		fprintf(fp, "%x", data[i]);
	    
    //fprintf(fp, " ");
}

void init_buffer(unsigned char *buffer, unsigned long long numbytes)
{
	for (unsigned long long i = 0; i < numbytes; i++)
		buffer[i] = (unsigned char)i;
}
