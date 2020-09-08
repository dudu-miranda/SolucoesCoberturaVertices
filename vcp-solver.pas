{	VERTEX COVER SOLVER (vcp-solver)
	
	NOMES
		ANA FLÁVIA FARIA PEREIRA		MATRÍCULA:0002788
		BRENO LAUREANO DE MELO			MATRÍCULA:0029054
		EDUARDO GABRIEL REIS MIRANDA	MATRÍCULA:0026495
		ITALO HAYLANDER FARIA GALVÃO	MATRÍCULA:0026894
		
	Compilação no Free Pascal Compiler, preferencialmente em sistema operacional Linux Ubuntu!
	Desenvolvido em ambiente Notepad++, Free Pascal.
	
	30/11/2016
	
	O objetivo deste software é resolver o problema chamado de Problema de Cobertura de Vertices(PCV),
	usando métodos deterministicos e heurísticos.
}

program vcp_solver;

uses
  Crt,SysUtils;

type Matriz = array of array of byte;

{	VARIAVEIS GLOBAIS
		mfinal do tipo Matriz, é a matriz configurada pelas função do método escolhido. 
		diretorio é onde o arquivo de benchmark se encontra, que por sua vez é atribuido pelo terceiro parametro informado pelo usuário.
		N é a quantidade de nós lida nas primeiras linhas do arquivo de benchmark.
		edge é quantidade de arcos lida nas primeiras linhas do arquivo de benchmark.
		metodo é o médoto escolhido pelo usuário, que por sua vez é  atribuido pelo segundo parametro informado pelo usuário.
		s1 é a semente escolhida pelo usuário, que por sua vez é  atribuido pelo primeiro parametro informado pelo usuário.
		saida é em qual diretorio será salvo o arquivo de log(resultados), que por sua vez é atribuido pelo quarto parametro informado pelo usuário.
		semente é atribuida por s1, que posteriormente é utilizada para mudar a semente para a função RandSeed.
		card é a cardinalidade final do método, que por sua vez é atribuida pela função boraacharacardinalidade,
		onde conta quantas relações existentes na matriz mfinal.
}
var matriz1,mfinal: Matriz; 
    diretorio,N,edge,metodo,s1,saida:string;
    semente,card:integer;
	REPETICOES:integer;
	
	

{ A estratégia utilizada para a leitura dos arquivos foi a seguinte.
Considerando que todo arquivo tem o padrão de cada letra de uma linha ser C, E ou P demos um tipo de 
tratamento para cada uma dessas linhas.
Caso a primeira letra fosse C simplesmente ignoramos e fomos a proxima linha, caso fosse P concatenamos
as strings para achar o numero de arcos, de nós.
Caso a primeira letra fosse E, nos concatenamos as strings referentes a cada numero pra adquirir as duas
cordenadas, e logo após isso colocamos como true na matriz nxn o vertice dos dois numeros lidos.}
procedure learquivo(var m:matriz; var n,edge:string);
var a1,a2,i,j:integer;
	aa1,aa2:string;
	linha:string;
	text:textfile;

begin

assign(text, diretorio);
reset(text);

while not
eof(text) do
begin

readln(text,linha);

if linha[1]='p' then
begin

i:=8;
n:='';
edge:='';
	while linha[i]<>' ' do
		begin
		n:=n+linha[i];
		inc(i);
		end;

	while i<>length(linha) do
	    begin
		inc(i);
		edge:=edge+linha[i];
		end;

setlength(m,strtoint(n),strtoint(n));

for i:=0 to length(m)-1 do
	for j:=0 to length(m)-1 do
	    m[i,j]:=0;

end

else if linha[1]='c' then
begin
end

else {e 16 97}
begin
aa1:='';
aa2:='';
i:=3;
while linha[i]<>' ' do
begin
   aa1:=aa1+linha[i];
   inc(i);
end;

while i<>length(linha) do
begin
   inc(i);
   aa2:=aa2+linha[i];

end;
a1:=strtoint(aa1);
a2:=strtoint(aa2);

m[a1-1,a2-1]:=1;
m[a2-1,a1-1]:=1;

end;

end;


close(text);
end;
//-----------------------------------------------


{	Essa função é responsável por verificar se a matriz de adjacência original
	está cheia, caso ela esteja cheia a função retorna 'true' caso contrário 'false'.
	Enquanto houver relação na matriz o algoritimo continua a dar sequencia até que a 
	matriz esteja vazia,quando a matriz estiver vazia o procedimento encerra, quando isso 
	acontece quer dizer que o algoritimo encontrou a cobertura de vertices.	}
function VerificaMatrizCheia(E:Matriz):Boolean;
var i,j:integer;
begin

VerificaMatrizcheia:=false;

	
	For i:= 0 to length(E)-1 do
	begin
		For j:= 0 to length(E)-1 do
			begin
				if  E[i,j] = 1 then
				begin
					VerificaMatrizCheia:= True;
					Exit;
				end;

			end;
	end;

end;
//----------------------------------------------------------------



{	Essa função é responsável por setar a  matriz que será 
	criada com a quantidade de nós lida no arquivo, como vazia.
	Que posteriormente recebera as relações dependendo método escolhido. }
procedure CriarMatrizVazia(var C: Matriz);
var i,j: integer;
begin
	For i:= 0 to length(C)-1 do
	begin
		For j:= 0 to length(C)-1 do
		begin
			C[i,j]:=0;
		end;
	end;
end;
//------------------------------------------------------------------



{	Esta função é responsável por remover as relações da matriz original
	de acordo com a necessidade de cada um dos métodos.	}
function ZeraRelacao(MatrizE:Matriz;IndiceA,indiceB:integer):Matriz;
var i:integer;
begin
	For i:= 0 to length(MatrizE)-1 do  //É necessário que a matriz seja percorrida somente em uma linha com a permutação das linhas e colunas.
        begin                          //Mantendo o indice da linha fixa, variando as colunas e vice-versa.
          MatrizE[indicea,i]:=0;
          MatrizE[i,indicea]:=0;
          MatrizE[indiceb,i]:=0;
          MatrizE[i,indiceb]:=0;
	end;

  ZeraRelacao:= MatrizE;

end;
//--------------------------------------------------------------------



{	Essa função é responsável pelo metodo aproximado.
	Enquanto a matriz original  não estiver vazia, sorteia-se uma posição até a mesma tenha relação, 
	e adicionada a matriz de cardinalidade. E a cada iteração é retirada todas as relações incidentes
	a posição sorteada na matriz original e verificado se a mesma esta vazia.	}
function MetodoAproximado:Matriz;
var C,E: Matriz;
    indiceA,indiceB:integer;
    Controle:Boolean;

begin


	LeArquivo(E,N,edge);
	matriz1:=E;

	SetLength(C, StrToInt(N),StrToInt(N)); //Seta o tamanho da matriz de cardinalidade de acordo com a quantidade de nos lidos no arquivo. 

	CriarMatrizVazia(C); //Preenche a matriz de cardinalidade toda em zeros. Portanto, uma matriz vazia.

	Controle:=true;

	While Controle = True do
	begin

	repeat
		IndiceA:=Random(strtoint(N));
		IndiceB:=Random(strtoint(N));
	Until E[IndiceA,IndiceB]= 1;

	C[indiceA,indiceA]:= 1;
	C[indiceB,indiceB]:=1;

	E:= ZeraRelacao(E,indiceA,indiceB); //Zera as posições incidentes a posição sorteada.

    Controle:= VerificaMatrizCheia(E); //Se a matriz original estiver vazia Controle recebe false e sai do laço.
	end;

	MetodoAproximado:= C;
end;
//---------------------------------------------------------



{	Esta função conta quantas relações existe na matriz de cardinalidade depois de executado o metodo desejado.	}
function boraacharacardinalidade(z:matriz):integer;
var i,j,c:integer;

begin

c:=0;

for i:=0 to length(z)-1 do
  for j:=i to length(z)-1 do
   begin
  	if z[i,j]=1 then
        begin
	    c:=c+1;        
        end;
   end;		
  

boraacharacardinalidade:=c;

end;
//------------------------------------------------------------



{ A função para se achar o vertice funciona da seguinte maneira.
Um vetor dinâmico que vai conter o seu indice na matriz e a quantidade de ligações que
ele possui. Se inicia esse vetor com uma ligação negativa para que não tenha nenhum problema
com lixo de memória. A cada iteração de leitura de uma linha voce tera a quantidade de ligações
de determinado vertice da matriz, tendo isso em mente, basta comparar a quantidade de ligações 
encontrada com a quantidade armazenada no vetor.
Se a encontrada for maior você apaga todo o vetor e coloca essa nova quantidade juntamente com 
o vertice referente, caso seja igual você adiciona um no tamanho do vetor e coloca o vertice 
referente na nova posição, e caso seja menor não se faz nada pois por hora este vertice não nos 
interessa.
No fim basta sortear o indice de algum dos vertices que estão no vetor.}
function acha_vertice(a:matriz):integer;
type vertice=record
			 vertice:integer;
			 ligacao:integer;
			 end;
var i,j,cont:integer;
    aux:array of vertice;

begin

setlength(aux,1);
aux[0].ligacao:=-5;

for i:=0 to length(a)-1 do
 begin
   cont:=0;
	 for j:=0 to length(a)-1 do
	 begin
		 if a[i,j]=1 then
		   begin
		   cont:=cont+1;
		   end;
	 end;

 if cont = aux[0].ligacao then
   begin
   setlength(aux,length(aux)+1);
   aux[length(aux)-1].vertice:=i;
   aux[length(aux)-1].ligacao:=cont;
   end

 else if cont>aux[0].ligacao then
         begin
		 setlength(aux,0);
		 setlength(aux,1);
		 aux[0].vertice:=i;
		 aux[0].ligacao:=cont;
		 end

 else begin
	  end;
 end;

 acha_vertice:=aux[random(length(aux))].vertice;

end;
//------------------------------------------------------



{ O metodo guloso utiliza muitas das funções usadas no metodo aproximado, porem a diferença
entre eles é que o metodo guloso sempre busca um dos vertices que possui mais ligações ao invés de 
sortear dois numeros aleatorios e colocar esse vertice na matriz final.
Tirando essa diferença o guloso funciona da mesma maneira do metodo aproximado}
function MetodoGuloso:Matriz;
var C,E: Matriz;
    indiceA,indiceB:integer;
    Controle:Boolean;

begin


        LeArquivo(E,N,edge);
        matriz1:=E;

	SetLength(C, StrToInt(N),StrToInt(N));

	CriarMatrizVazia(C);

	Controle:=true;

	While Controle = True do
	begin


    IndiceA:=acha_vertice(E);
    IndiceB:=indiceA;


	C[indiceA,indiceB]:= 1;

	Matriz1:= ZeraRelacao(E,indiceA,indiceB);

    Controle:= VerificaMatrizCheia(E);

	end;

	MetodoGuloso:= C;
end;
//-----------------------------------------------------------------------



{	Procedimento que recebe os nos, arcos, metodo, instancia, saida para os resultados,
	a semente e a cardinalidade, para impressão na tela do usuário.	}
procedure SaidaTerminal(n,edge,metodo,diretorio,saida:string; semente,card:integer);
begin
	 writeln ('Veterx Cover Solver');
	 writeln ('');
	 writeln ('Nodes: ', n);
	 writeln ('Arcs: ', edge);
	 writeln ('');
	 writeln ('Seed: ', semente);
	 writeln ('Method: ', metodo);
	 writeln ('Input: ', diretorio);
	 writeln ('Output: ',saida);  
	 writeln ('');
	 writeln ('Cover: ', card);
	 writeln ('');
	 writeln ('End of processing.');
end;
//-----------------------------------------------------------------------------



{	Procedimento que armazena os parametros e resultados em arquivo de texto.	}
procedure ArquivoLog(Nos,Arcos,Metodo,Instancia,NomeDoArquivo:string; Semente,Cobertura:integer);
var Arquivo: TextFile;
begin
	Assign(Arquivo, NomeDoArquivo);

	if FileExists(NomeDoArquivo) then
	begin
		Append(Arquivo);
		Writeln(Arquivo, Instancia+#09+Nos+#09+Arcos+#09+IntToStr(Semente)+#09+Metodo+#09+IntToStr(Cobertura));

	end else
	begin
		ReWrite(Arquivo);
		Writeln(Arquivo, 'INSTANCE'+#09+'NODES'+#09+'ARCS'+#09+'SEEDS'+#09+'METHOD'+#09+'COVER');
    	Writeln(Arquivo, Instancia+#09+Nos+#09+Arcos+#09+IntToStr(Semente)+#09+Metodo+#09+IntToStr(Cobertura));
	end;

	Close(Arquivo);

end;
//----------------------------------------------------------------------------------------------------------------------//
//			                                Fim dos procedimentos e funções!											//


begin

  if paramcount=4 then
  begin

    {	Atribui as variaveis, os parametros informados pelo o usuário.	}
	s1:=paramstr(1);
    semente:=strtoint(s1);
	randseed:=semente;

	diretorio:=paramstr(3);
	
    metodo:=paramstr(2);

    saida:=paramstr(4);
	
	REPETICOES:=0;


case metodo of

  'A','a':  begin
				{while REPETICOES < 100 do
				begin
				REPETICOES:= REPETICOES+1;
				
				semente:= Random(10000);}
				
				mfinal:=MetodoAproximado; //A matriz final recebe a função que retorna a matriz de cardinalidade preenchida.
				card:=boraacharacardinalidade(mfinal); //A variavel card recebe da funçao que conta quantas relações existe na matriz de cardinalidade.
				
				//ClrScr;
				
				SaidaTerminal(N,edge,metodo,diretorio,saida,semente,card);
				ArquivoLog(N,edge,metodo,diretorio,saida,semente,card);
				
				{Writeln('Execusao No. ',REPETICOES);
			
				Delay(1000);
				
				
				end;}
			end;

  'G','g':	begin
				{while REPETICOES < 100 do
				begin
				REPETICOES:=REPETICOES+1;
				
				semente:= Random(10000);}
				
				mfinal:=MetodoGuloso;
				card:=boraacharacardinalidade(mfinal);
				
				//ClrScr;
				
				SaidaTerminal(N,edge,metodo,diretorio,saida,semente,card);
				ArquivoLog(N,edge,metodo,diretorio,saida,semente,card);
				
				{Writeln('Execusao No. ',REPETICOES);
			
				Delay(1000);
				end;}
			end;

end;
	read;
	
	//SaidaTerminal(N,edge,metodo,diretorio,saida,semente,card);
	//ArquivoLog(N,edge,metodo,diretorio,saida,semente,card);

end

else begin
	 writeln('Numero de parametros incorretos!');
	 end;

end.
