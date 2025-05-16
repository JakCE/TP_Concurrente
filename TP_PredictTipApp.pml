#define wait(s) atomic { (s > 0) -> s-- }
#define signal(s) s++

// Variables compartidas
byte mutex = 1;
int peso[5] = 0;

proctype EntrenamientoBatch() {
    int i = 0;
    int grad[5];
    
    printf("Proceso %d: calculando gradientes...\n", _pid);

    // Simula cálculo del gradiente (simplificado)
    do
    :: (i < 5) ->
        grad[i] = 1;
        i++
    :: else -> break
    od;

    printf("Proceso %d: esperando para entrar a sección crítica...\n", _pid);
    wait(mutex);
    printf("Proceso %d: ENTRÓ a sección crítica.\n", _pid);

    i = 0;
    do
    :: (i < 5) ->
        peso[i] = peso[i] + grad[i];
        i++
    :: else -> break
    od;

    printf("Proceso %d: saliendo de sección crítica.\n", _pid);
    signal(mutex);
}

init {
    run EntrenamientoBatch();
    run EntrenamientoBatch();
}