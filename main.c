#include <stdio.h>
#include <stdlib.h>
int main(){
    char c[] ={'h','e','y','\0'};
    char *d = malloc(4);
    for (int i=0; i<4; i++){
        *(d+i) = c[i];
    }
    printf("%s\n",d);
    free(d);
    return 0;
}
