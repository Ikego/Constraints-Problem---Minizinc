% Use this editor as a MiniZinc scratch book
include "globals.mzn";


predicate count(array [$X] of var int: x, var int: y, var int: c);


%General
int: muelles;
int: barcos;

array[int] of int: B_codigoBarcos; %Barcos
array[int] of int: B_tpEspera;     %Tiempo maximo de espera
array[int] of int: B_tpdescarga;   %Tiempo de descarga
array[int, 1..3] of 0..1: B_estadost;%Condiciones de clima
array[int, 1..3] of 0..1: B_estadosm;%Condiciones de marea

array[int] of int: M_codigoMuelles;%Muelles

array[int] of 1..3: P_estadost;     %Estados del tiempo en el puerto
array[int] of 4..6: P_estadosm;     %Estados de la marea en el puerto

%Restricciones Adicionales:
array[int, 1..2] of int: horaFlexible;
array[int, 1..2] of int: horaLlegada;
array[int, 1..2] of int: horasHabiles;


%Array variables para podar los valores de los tiempos en los que los muelles no estaran disponibles (mareas y clima)
array[1..round(length(horasHabiles)/2), 1..length(P_estadost)] of var 0..3: P_estadostUsar;

%Array variables para podar los tiempos de los muelles que no van a estar disponibles (mareas y clima)
array[1..muelles, 1..length(P_estadost)] of var 0..3: P_estadostFinal;

%Array variable para marcas la estadia de cada barco en un muelle en concreto
array[1..muelles, 1..length(P_estadost)] of var 0..barcos: usoMuelle;
array[1..barcos, 1..length(P_estadost)] of var 0..barcos: tiempoPorBarco;

array[1..barcos,1..5] of var int: respuesta;

%%MANEJO DE MUELLE
%maxima distancia
constraint forall(j in 1..barcos, m in 1..muelles)( sum([usoMuelle[m,i]|i,n in 1..length(P_estadost) where usoMuelle[m,i] = j /\ usoMuelle[m,n] = j /\ i != n /\ abs(i-n) >= B_tpdescarga[j]]) = 0 ); %miedo

%cantidad por muelle
constraint forall(j in 1..barcos, m in 1..muelles)( (sum([1|i in 1..length(P_estadost) where usoMuelle[m,i] = j]) = B_tpdescarga[j]) xor (sum([1|i in 1..length(P_estadost) where usoMuelle[m,i] = j]) = 0) );

%cantidad total
constraint forall(i in 1..barcos)( count(usoMuelle,i,B_tpdescarga[i]) );

%no uso del Muelle en tiempos restringidos
constraint forall(i in 1..muelles, j in 1..length(P_estadost) where P_estadostFinal[i,j] = 0)(usoMuelle[i,j] = 0);

%copia de uso de muelle a la totalidad de cada barco
constraint forall(i in 1..muelles, j in 1..length(P_estadost) where usoMuelle[i,j] > 0)(tiempoPorBarco[usoMuelle[i,j],j] = usoMuelle[i,j]);


%MANEJO DE BARCO
%limpiar totalidad de cada barco.
constraint forall(i in 1..barcos, j in 1..length(P_estadost) where tiempoPorBarco[i,j] != i)(tiempoPorBarco[i,j] = 0);

%cantidad maxima del barco en el puerto (descarga+espera)
constraint forall(i in 1..barcos)( sum([1|j in 1..length(P_estadost) where tiempoPorBarco[i,j] = i]) >= B_tpdescarga[i] );
constraint forall(i in 1..barcos)( sum([1|j in 1..length(P_estadost) where tiempoPorBarco[i,j] = i]) <= (B_tpEspera[i] + B_tpdescarga[i]));

%distancia maxima
constraint forall(j in 1..barcos)( sum([tiempoPorBarco[j,i]|i,n in 1..length(P_estadost) where tiempoPorBarco[j,i] = j /\ tiempoPorBarco[j,n] = j /\ i != n /\ abs(i-n) >= (B_tpdescarga[j] + B_tpEspera[j])]) = 0 );

%barco n llega desde x slot
constraint forall(i in 1..round(length(horaLlegada)/2))( if horaFlexible[i,2] = 1 then (if i = 1 then tiempoPorBarco[horaLlegada[i,1],horaLlegada[i,2]] = horaLlegada[i,1] else tiempoPorBarco[horaLlegada[i,1],horaLlegada[i,2]] = horaLlegada[i,1] /\ tiempoPorBarco[horaLlegada[i,1],horaLlegada[i,2]-1] != horaLlegada[i,1]  endif) else (if i = 1 then (tiempoPorBarco[horaLlegada[i,1],horaLlegada[i,2]] = horaLlegada[i,1]) xor (tiempoPorBarco[horaLlegada[i,1],horaLlegada[i,2]] != horaLlegada[i,1]) else (tiempoPorBarco[horaLlegada[i,1],horaLlegada[i,2]] = horaLlegada[i,1] /\ tiempoPorBarco[horaLlegada[i,1],horaLlegada[i,2]-1] != horaLlegada[i,1] ) xor (tiempoPorBarco[horaLlegada[i,1],horaLlegada[i,2]] != horaLlegada[i,1]) endif) endif ); 

%revision condiciones climaticas
constraint forall(i in 1..barcos, j in 1..length(P_estadost) where tiempoPorBarco[i,j] = i)(if (P_estadost[j] = 1 /\ B_estadost[i, 1] = 1) then true elseif (P_estadost[j] = 2 /\ B_estadost[i, 2] = 1) then true elseif (P_estadost[j] = 3 /\ B_estadost[i, 3] = 1) then true else false endif);

%revision condiciones de marea
constraint forall(i in 1..barcos, j in 1..length(P_estadost) where tiempoPorBarco[i,j] = i)(if (P_estadosm[j] = 4 /\ B_estadosm[i, 1] = 1) then true elseif (P_estadosm[j] = 5 /\ B_estadosm[i, 2] = 1) then true elseif (P_estadosm[j] = 6 /\ B_estadosm[i, 3] = 1) then true else false endif);


%OTROS


%Limpiar disponibilidad de los muelles (mareas y clima)
constraint forall(i in 1..(round(length(horasHabiles)/2))) ( forall(m in 1..(round(length(horasHabiles)/2)), n in 1..length(P_estadost) 
                  where m = i )( if (n <= horasHabiles[i,2] /\ n >= horasHabiles[i,1]) then P_estadostUsar[m,n] = P_estadost[n] else P_estadostUsar[m,n] = 0 endif));


%Limpiar tiempos de muelles que no estan disponibles(mareas y clima)
constraint forall(i in 1..muelles, j in 1..length(P_estadost))(P_estadostFinal[i,j] = P_estadostUsar[i,j]);


%Respuesta
constraint forall(i in 1..barcos, j in 1..length(P_estadost) where tiempoPorBarco[i,j] = i)(respuesta[i,1] = B_codigoBarcos[i]);
constraint forall(i in 1..barcos, j in 1..length(P_estadost), m in 1..muelles where usoMuelle[m,j] = i)(respuesta[i,2] = M_codigoMuelles[m]);
constraint forall(i in 1..barcos)(respuesta[i,3] = min([j|j in 1..length(P_estadost) where tiempoPorBarco[i,j] = i]));
constraint forall(i in 1..barcos)(respuesta[i,4] = min([j|m in 1..muelles, j in 1..length(P_estadost) where usoMuelle[m,j] = i]));
constraint forall(i in 1..barcos)(respuesta[i,5] = max([j|m in 1..muelles, j in 1..length(P_estadost) where usoMuelle[m,j] = i]));

solve satisfy;


output  [ show_int(1,respuesta[i,j]) ++ " " ++ 
         if j mod 5 == 0 then "\n" else " " endif
         | i in 1..barcos ,j in 1..5 ] ++ ["\n"];

