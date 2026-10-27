using System;
using System.Collections.Generic;
using System.Text;

// ============================================================
// Simulador de escalonador de transações com 2PL Strict
// ============================================================

// Uma operação da história: r (leitura), w (escrita) ou c (commit).
// Em 'w' sem valor (ex.: w1[x]), o dado é incrementado em 1 na hora da execução.
class Operacao
{
    public int Transacao;
    public char Tipo;       // 'r', 'w' ou 'c'
    public string Dado;     // vazio no commit
    public bool TemValor;   // só vale para escrita
    public int Valor;

    public Operacao(int transacao, char tipo, string dado, bool temValor, int valor)
    {
        Transacao = transacao;
        Tipo = tipo;
        Dado = dado;
        TemValor = temValor;
        Valor = valor;
    }

    public override string ToString()
    {
        if (Tipo == 'r')
            return $"r{Transacao}[{Dado}]";
        if (Tipo == 'w')
        {
            if (TemValor)
                return $"w{Transacao}[{Dado},{Valor}]";
            return $"w{Transacao}[{Dado}]";
        }
        return $"c{Transacao}";
    }
}

// Linha da tabela de locks de um dado:
//  - Leitores: transações com lock compartilhado (S)
//  - Escritor: transação com lock exclusivo (X), ou -1 se ninguém tem
class LockInfo
{
    public List<int> Leitores = new List<int>();
    public int Escritor = -1;
}

// Guarda o valor antigo de um dado, para desfazer a escrita se a transação abortar.
class RegistroUndo
{
    public string Dado;
    public int ValorAnterior;

    public RegistroUndo(string dado, int valorAnterior)
    {
        Dado = dado;
        ValorAnterior = valorAnterior;
    }
}

class Simulador
{
    const int NENHUM = -1;

    // ---------- estruturas de dados ----------
    private List<Operacao> _hi;                                           // história inicial (cresce quando uma transação é reinserida)
    private List<Operacao> _hf = new List<Operacao>();                    // história final
    private SortedDictionary<string, int> _dados = new SortedDictionary<string, int>();   // banco de dados em memória
    private SortedDictionary<string, LockInfo> _locks = new SortedDictionary<string, LockInfo>(); // tabela de locks
    private Dictionary<int, List<Operacao>> _opsTx = new Dictionary<int, List<Operacao>>(); // operações originais de cada transação
    private Dictionary<int, Queue<Operacao>> _esperas = new Dictionary<int, Queue<Operacao>>();  // fila de delay de cada transação
    private Dictionary<int, List<RegistroUndo>> _undo = new Dictionary<int, List<RegistroUndo>>(); // log para rollback
    private List<int> _bloqueadas = new List<int>();                      // transações em delay, na ordem em que bloquearam
    private int _pos;        // posição da operação atual na HI
    private int _deadlocks;

    // variáveis usadas pela DFS que procura ciclo no grafo de espera
    private Dictionary<int, List<int>> _grafo = new Dictionary<int, List<int>>();
    private Dictionary<int, int> _estado = new Dictionary<int, int>();   // 1 = na pilha, 2 = terminado
    private List<int> _pilha = new List<int>();
    private List<int> _ciclo = new List<int>();

    public Simulador(List<Operacao> hi)
    {
        _hi = new List<Operacao>(hi);

        foreach (Operacao op in hi)
        {
            int t = op.Transacao;

            // primeira vez que a transação aparece: cria suas estruturas
            if (!_opsTx.ContainsKey(t))
            {
                _opsTx[t] = new List<Operacao>();
                _esperas[t] = new Queue<Operacao>();
                _undo[t] = new List<RegistroUndo>();
            }
            _opsTx[t].Add(op);

            // cada dado usado na HI começa com valor 0 e ganha uma linha na tabela de locks
            if (op.Tipo != 'c' && !_dados.ContainsKey(op.Dado))
            {
                _dados[op.Dado] = 0;
                _locks[op.Dado] = new LockInfo();
            }
        }
    }

    // ============================================================
    // Laço principal: envia as operações da HI ao escalonador, na ordem
    // ============================================================
    public void Simular()
    {
        Console.WriteLine("HI: " + string.Join(" ", _hi));
        Console.WriteLine();

        // for com índice (e não foreach) porque a HI cresce quando uma transação abortada é reinserida
        for (_pos = 0; _pos < _hi.Count; _pos++)
        {
            Operacao op = _hi[_pos];
            Console.WriteLine($"--- Passo {_pos + 1}: chega {op} ---");

            Chegar(op);
            Estabilizar();
            ImprimirEstado();
            Console.WriteLine();
        }

        ImprimirResultado();
    }

    // Trata uma operação que acabou de chegar da HI.
    private void Chegar(Operacao op)
    {
        int t = op.Transacao;

        // transação já em delay: a operação só entra na fila de espera dela
        if (_bloqueadas.Contains(t))
        {
            _esperas[t].Enqueue(op);
            Console.WriteLine($"  T{t} está em delay; {op} entra na fila de espera da transação.");
            return;
        }

        // não consegue o lock: a transação entra em delay
        if (!PodeExecutar(op))
        {
            _bloqueadas.Add(t);
            _esperas[t].Enqueue(op);
            string tipoLock = "exclusivo";
            if (op.Tipo == 'r')
                tipoLock = "compartilhado";
            Console.WriteLine($"  {op} não consegue o lock {tipoLock} em {op.Dado} (conflito com {ListaT(Conflitantes(op))}). T{t} entra em DELAY.");
            return;
        }

        Aplicar(op, false);
    }

    // Tira do delay quem pode; depois, se houver deadlock, resolve e repete.
    private void Estabilizar()
    {
        do
        {
            ResolverEsperas();
        } while (DetectarEResolverUmDeadlock());
    }

    // ============================================================
    // Locks
    // ============================================================

    // Lista as transações que impedem a operação de obter o lock que ela precisa.
    //  - leitura (S): conflita com outro escritor
    //  - escrita (X): conflita com outro escritor e com qualquer outro leitor
    private List<int> Conflitantes(Operacao op)
    {
        List<int> resultado = new List<int>();
        if (op.Tipo == 'c')
            return resultado;

        LockInfo info = _locks[op.Dado];
        int t = op.Transacao;

        if (info.Escritor != NENHUM && info.Escritor != t)
            resultado.Add(info.Escritor);

        if (op.Tipo == 'w')
        {
            foreach (int leitor in info.Leitores)
            {
                if (leitor != t)
                    resultado.Add(leitor);
            }
        }
        return resultado;
    }

    private bool PodeExecutar(Operacao op)
    {
        return Conflitantes(op).Count == 0;
    }

    private void ConcederLock(Operacao op)
    {
        int t = op.Transacao;
        LockInfo info = _locks[op.Dado];

        if (op.Tipo == 'r')
        {
            // já tem S ou X neste dado: não precisa de lock novo
            if (info.Escritor == t || info.Leitores.Contains(t))
                return;

            info.Leitores.Add(t);
            Console.WriteLine($"  lock: sl{t}[{op.Dado}] concedido (compartilhado).");
        }
        else
        {
            if (info.Escritor == t)
                return;

            // se a transação já era leitora, é um upgrade de S para X
            bool upgrade = info.Leitores.Remove(t);
            info.Escritor = t;

            if (upgrade)
                Console.WriteLine($"  lock: xl{t}[{op.Dado}] concedido (upgrade S -> X).");
            else
                Console.WriteLine($"  lock: xl{t}[{op.Dado}] concedido (exclusivo).");
        }
    }

    // Strict 2PL: todos os locks da transação são liberados juntos, no commit (ou no abort).
    private void LiberarLocks(int t)
    {
        string liberados = "";

        foreach (KeyValuePair<string, LockInfo> par in _locks)
        {
            LockInfo info = par.Value;

            if (info.Escritor == t)
            {
                info.Escritor = NENHUM;
                liberados += $" ul{t}[{par.Key}]";
            }
            if (info.Leitores.Remove(t))
                liberados += $" ul{t}[{par.Key}]";
        }

        _bloqueadas.Remove(t);
        _esperas[t].Clear();

        if (liberados == "")
            Console.WriteLine($"  unlock: T{t} não possuía locks.");
        else
            Console.WriteLine($"  unlock:{liberados}.");
    }

    // ============================================================
    // Execução de operações
    // ============================================================

    // Executa uma operação que já pode rodar (o lock está liberado) e coloca na HF.
    private void Aplicar(Operacao op, bool vindaDoDelay)
    {
        int t = op.Transacao;
        string sufixo = "";
        if (vindaDoDelay)
            sufixo = " [executada após delay]";

        if (op.Tipo == 'c')
        {
            _hf.Add(op);
            _undo[t].Clear();
            Console.WriteLine($"  {op}{sufixo}: commit de T{t}; vai para a HF.");
            LiberarLocks(t);
            return;
        }

        ConcederLock(op);

        if (op.Tipo == 'r')
        {
            _hf.Add(op);
            Console.WriteLine($"  {op}{sufixo}: lê {op.Dado} = {_dados[op.Dado]}; vai para a HF.");
        }
        else
        {
            int antigo = _dados[op.Dado];
            int novo;
            if (op.TemValor)
                novo = op.Valor;
            else
                novo = antigo + 1;

            _undo[t].Add(new RegistroUndo(op.Dado, antigo));
            _dados[op.Dado] = novo;
            _hf.Add(op);
            Console.WriteLine($"  {op}{sufixo}: escreve {op.Dado} = {novo} (antes: {antigo}); vai para a HF.");
        }
    }

    // Tenta executar, em ordem, as operações que estão em delay.
    // A transação só sai de _bloqueadas quando a fila dela esvazia; se a próxima
    // operação ainda conflita, ela continua em delay.
    private void ResolverEsperas()
    {
        bool progresso;

        do
        {
            progresso = false;

            // cópia da lista, porque _bloqueadas muda durante o laço
            List<int> copia = new List<int>(_bloqueadas);
            foreach (int t in copia)
            {
                Queue<Operacao> fila = _esperas[t];
                bool executou = false;

                while (fila.Count > 0 && PodeExecutar(fila.Peek()))
                {
                    Operacao prox = fila.Dequeue();
                    Aplicar(prox, true);
                    executou = true;
                    progresso = true;
                }

                if (fila.Count == 0)
                {
                    _bloqueadas.Remove(t);
                    if (executou)
                        Console.WriteLine($"  T{t} saiu do delay.");
                }
            }
        } while (progresso);
    }

    // ============================================================
    // Deadlock: grafo de espera + DFS
    // ============================================================

    // Aresta Ti -> Tj: a operação em delay de Ti precisa de um lock que Tj tem.
    private Dictionary<int, List<int>> MontarGrafoEspera()
    {
        Dictionary<int, List<int>> grafo = new Dictionary<int, List<int>>();

        foreach (int t in _bloqueadas)
        {
            Queue<Operacao> fila = _esperas[t];
            if (fila.Count > 0)
                grafo[t] = Conflitantes(fila.Peek());
            else
                grafo[t] = new List<int>();
        }
        return grafo;
    }

    // Procura um ciclo com DFS. Devolve a lista de transações do ciclo (vazia se não houver).
    private List<int> EncontrarCiclo(Dictionary<int, List<int>> grafo)
    {
        _grafo = grafo;
        _estado = new Dictionary<int, int>();
        _pilha = new List<int>();
        _ciclo = new List<int>();

        foreach (int no in grafo.Keys)
        {
            if (!_estado.ContainsKey(no))
            {
                Visitar(no);
                if (_ciclo.Count > 0)
                    return _ciclo;
            }
        }
        return _ciclo;
    }

    private void Visitar(int atual)
    {
        _estado[atual] = 1;       // entrou na pilha
        _pilha.Add(atual);

        if (_grafo.ContainsKey(atual))
        {
            foreach (int prox in _grafo[atual])
            {
                if (!_estado.ContainsKey(prox))
                {
                    Visitar(prox);
                }
                else if (_estado[prox] == 1)
                {
                    // voltou para um nó que ainda está na pilha: achou o ciclo
                    int inicio = _pilha.IndexOf(prox);
                    for (int i = inicio; i < _pilha.Count; i++)
                        _ciclo.Add(_pilha[i]);
                }

                if (_ciclo.Count > 0)
                    return;
            }
        }

        _pilha.RemoveAt(_pilha.Count - 1);
        _estado[atual] = 2;       // terminou
    }

    // Resolve um ciclo por chamada; Estabilizar repete enquanto houver ciclos.
    private bool DetectarEResolverUmDeadlock()
    {
        List<int> ciclo = EncontrarCiclo(MontarGrafoEspera());
        if (ciclo.Count == 0)
            return false;

        _deadlocks++;
        Console.WriteLine($"  *** DEADLOCK #{_deadlocks} detectado: o grafo de espera tem um ciclo ***");

        for (int i = 0; i < ciclo.Count; i++)
        {
            int de = ciclo[i];
            int para = ciclo[(i + 1) % ciclo.Count];
            Operacao pendente = _esperas[de].Peek();
            Console.WriteLine($"    T{de} espera T{para}  ({pendente} precisa de lock em {pendente.Dado})");
        }

        // Critério: aborta a transação mais nova do ciclo, isto é, a de maior número.
        // O número não muda quando a transação é reiniciada.
        int vitima = ciclo[0];
        foreach (int t in ciclo)
        {
            if (t > vitima)
                vitima = t;
        }

        Console.WriteLine($"  Critério: abortar a transação mais nova do ciclo (maior número). Vítima: T{vitima}.");
        Abortar(vitima);
        return true;
    }

    private void Abortar(int t)
    {
        Console.WriteLine($"  Abortando T{t}:");

        // 1) rollback: desfaz as escritas, da última para a primeira
        for (int i = _undo[t].Count - 1; i >= 0; i--)
        {
            RegistroUndo r = _undo[t][i];
            Console.WriteLine($"    rollback: {r.Dado} volta de {_dados[r.Dado]} para {r.ValorAnterior}.");
            _dados[r.Dado] = r.ValorAnterior;
        }
        _undo[t].Clear();

        // 2) retira as operações de T da HF
        int removidas = 0;
        for (int i = _hf.Count - 1; i >= 0; i--)
        {
            if (_hf[i].Transacao == t)
            {
                _hf.RemoveAt(i);
                removidas++;
            }
        }
        Console.WriteLine($"    {removidas} operação(ões) de T{t} retirada(s) da HF.");

        // 3) libera os locks e descarta a fila de delay
        LiberarLocks(t);

        // 4) tira da HI o que ainda restava da execução antiga de T (depois da posição atual)
        for (int i = _hi.Count - 1; i > _pos; i--)
        {
            if (_hi[i].Transacao == t)
                _hi.RemoveAt(i);
        }

        // 5) recoloca a transação inteira no final da HI
        _hi.AddRange(_opsTx[t]);
        Console.WriteLine($"    T{t} reinserida no final da HI.");
        Console.WriteLine("    HI restante: " + string.Join(" ", _hi.GetRange(_pos + 1, _hi.Count - _pos - 1)));
    }

    // ============================================================
    // Saída
    // ============================================================
    private string ListaT(List<int> ids)
    {
        string texto = "";
        foreach (int id in ids)
        {
            if (texto != "")
                texto += ", ";
            texto += "T" + id;
        }
        return texto;
    }

    private void ImprimirEstado()
    {
        // HF
        if (_hf.Count == 0)
            Console.WriteLine("  HF: (vazia)");
        else
            Console.WriteLine("  HF: " + string.Join(" ", _hf));

        // tabela de locks (só os dados que têm algum lock)
        string tabela = "";
        foreach (KeyValuePair<string, LockInfo> par in _locks)
        {
            LockInfo info = par.Value;
            string item = "";

            if (info.Escritor != NENHUM)
                item = $"{par.Key}: X(T{info.Escritor})";
            else if (info.Leitores.Count > 0)
                item = $"{par.Key}: S({ListaT(info.Leitores)})";

            if (item != "")
            {
                if (tabela != "")
                    tabela += " | ";
                tabela += item;
            }
        }
        if (tabela == "")
            tabela = "(nenhum)";
        Console.WriteLine("  Locks: " + tabela);

        // transações em delay, com as operações que aguardam
        string delays = "";
        foreach (int t in _bloqueadas)
        {
            if (delays != "")
                delays += "  ";
            delays += $"T{t}[{string.Join(" ", _esperas[t])}]";
        }
        if (delays == "")
            delays = "(nenhuma)";
        Console.WriteLine("  Delay: " + delays);
    }

    private void ImprimirResultado()
    {
        Console.WriteLine("=== HISTÓRIA FINAL (HF) =====");
        if (_hf.Count == 0)
            Console.WriteLine("(vazia)");
        else
            Console.WriteLine(string.Join(" ", _hf));
        Console.WriteLine();

        Console.WriteLine("=== VALORES FINAIS =====");
        foreach (KeyValuePair<string, int> item in _dados)
            Console.WriteLine($"{item.Key} = {item.Value}");
        Console.WriteLine();

        Console.WriteLine("=== RESUMO =====");
        Console.WriteLine($"Deadlocks detectados: {_deadlocks}");
    }
}

static class Program
{
    static void Main()
    {
        Console.OutputEncoding = Encoding.UTF8;   // para os acentos aparecerem no console

        Console.WriteLine("\n=== Simulador de Escalonamento Strict 2PL =====\n");
        Console.WriteLine("Insira a HI em uma linha, com as operações separadas por espaço (ex.: r1[x] w1[x] c1).");
        Console.WriteLine("Aceita [x] ou (x). Escrita sem valor incrementa o dado em 1; com valor: w1[x,5].");
        Console.Write("HI -> ");

        string? texto = Console.ReadLine();
        if (texto == null)
            texto = "";

        List<Operacao> hi = ParseHI(texto);

        Console.WriteLine();
        Simulador sim = new Simulador(hi);
        sim.Simular();
    }

    // Lê a HI (assume o formato correto), com as operações separadas por espaço:
    // r1[x]  w1[x]  w1[x,10]  c1   (também vale com parênteses: r1(x) w1(x,10))
    static List<Operacao> ParseHI(string texto)
    {
        List<Operacao> resultado = new List<Operacao>();

        // tira os espaços que estiverem dentro de [ ] ou ( ), por exemplo w1[x, 5]
        string limpo = "";
        bool dentroDosColchetes = false;
        foreach (char c in texto)
        {
            if (c == '[' || c == '(')
                dentroDosColchetes = true;
            if (c == ']' || c == ')')
                dentroDosColchetes = false;

            if (!(dentroDosColchetes && c == ' '))
                limpo += c;
        }

        foreach (string token in limpo.Split(' ', StringSplitOptions.RemoveEmptyEntries))
        {
            char tipo = char.ToLower(token[0]);

            if (tipo == 'c')
            {
                int tid = int.Parse(token.Substring(1));
                resultado.Add(new Operacao(tid, 'c', "", false, 0));
            }
            else
            {
                // r1[x], w1[x] ou w1[x,15]
                int abre = token.IndexOfAny(new char[] { '[', '(' });
                int fecha = token.IndexOfAny(new char[] { ']', ')' });
                int tid = int.Parse(token.Substring(1, abre - 1));
                string[] dentro = token.Substring(abre + 1, fecha - abre - 1).Split(',');
                string dado = dentro[0].ToUpper();

                int valor = 0;
                bool temValor = false;
                if (tipo == 'w' && dentro.Length == 2)
                {
                    valor = int.Parse(dentro[1]);
                    temValor = true;
                }

                resultado.Add(new Operacao(tid, tipo, dado, temValor, valor));
            }
        }
        return resultado;
    }
}