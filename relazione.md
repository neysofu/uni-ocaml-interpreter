---
title: Secondo Progetto Intermedio
author: Filippo Costa
date: Dicembre 2020
---

# 1. Introduzione

Questo progetto consiste in un interprete in OCaml di un semplice linguaggio di programmazione a paradigma funzionale. L'intero interprete è contenuto in un unico file sorgente con nome `interpreter.ml`. Il file `original.ml` contiene la versione originale dell'interprete del linguaggio (senza le modifiche apportate dal sottoscritto). Entrambi i file contengono ciascuno una batteria di test per verificare il corretto funzionamento del rispettivo interprete.

Per eseguire la batteria di test si può usare il comando `ocaml`:

    $ ocaml original.ml
    $ ocaml interpreter.ml

Rispetto alla versione originale, `interpreter.ml` aggiunge il supporto per *stringhe* e *insiemi*. Le stringhe sono sequenze immutabili di caratteri e gli insiemi sono collezioni immutabili e senza ordine di oggetti omogenei. Gli insiemi possono essere parametrizzati esclusivamente su `Int`, `Bool`, o `String` (i.e. non è possibile costruire insiemi di insiemi o insiemi di funzioni).

Il type checking è dinamico (a runtime).

# 2. Regole operazionali per `Set`

## 2.1. Introduzione del tipo di dato `Set`

$$
\frac
    {env \vartriangleright e \implies t \colon String, \ \ t \in \{"string", "int", "bool" \} }
    {env \vartriangleright \texttt{Eset}(e) \implies \emptyset \colon Set_t}
$$

$$
\frac
    {env \vartriangleright e_1 \implies t \colon String, \ \ t \in \{"string", "int", "bool" \}, \ \ env \vartriangleright e_2 \implies v \colon t }
    {env \vartriangleright \texttt{Singleton}(e_2, e_1) \implies \{ v \} \colon Set_t}
$$

## 2.2 Operazioni su `Set`
$$
\frac
    {env \vartriangleright s \implies A \colon Set_t, \ \ env \vartriangleright p \implies P \colon t \rightarrow Bool}
    {
        \begin{array}{l}
        {\forall x \in A \implies P(x) \vdash env \vartriangleright \texttt{ForAll}(p, s) \implies \top} \\
        {\forall x \in A \implies \neg P(x) \vdash env \vartriangleright \texttt{Exists}(p, s) \implies \bot} \\
        {\exists x \in A \mid P(x) \vdash env \vartriangleright \texttt{Exists}(p, s) \implies \top} \\
        {\exists x \in A \mid \neg P(x) \vdash env \vartriangleright \texttt{ForAll}(p, s) \implies \bot} \\
        {env \vartriangleright \texttt{Filter}(p, s) \implies B \colon Set_t, \ \ B \subset A, \ \ \forall x \in A \implies \left( P(x) \Longleftrightarrow x \in B \right)}
        \end{array}
    }
$$

$$
\frac
    {env \vartriangleright s_1 \implies A \colon Set_t, \ \ env \vartriangleright s_2 \implies B \colon Set_t}
    {
        \begin{array}{l}
        {env \vartriangleright \texttt{Union}(s_1, s_2) \implies A \cup B} \\
        {env \vartriangleright \texttt{Intersection}(s_1, s_2) \implies A \cap B} \\
        {env \vartriangleright \texttt{SetDifference}(s_1, s_2) \implies A \backslash B} \\
        {A \subset B \vdash env \vartriangleright \texttt{IsSubsetOf}(s_1, s_2) \implies \top} \\
        {A \not\subset B \vdash env \vartriangleright \texttt{IsSubsetOf}(s_1, s_2) \implies \bot}
        \end{array}
    }
$$

$$
\frac
    {env \vartriangleright s \implies A \colon Set_t, \ \ env \vartriangleright e \implies v \colon t}
    {
        \begin{array}{l}
        {env \vartriangleright \texttt{SetAdd}(s, e) \implies A \cup \{v\}} \\
        {env \vartriangleright \texttt{SetRemove}(s, e) \implies A \backslash \{v\}} \\
        {v \in A \vdash env \vartriangleright \texttt{IsIn}(e, s) \implies \top} \\
        {v \not\in A \vdash env \vartriangleright \texttt{IsIn}(e, s) \implies \bot} \\
        \end{array}
    }
$$

$$
\frac
    {env \vartriangleright s \implies A \colon Set_t}
    {
        \begin{array}{l}
        {A = \emptyset \vdash env \vartriangleright \texttt{IsEmpty}(s) \implies \top} \\
        {A \not = \emptyset \vdash env \vartriangleright \texttt{IsEmpty}(s) \implies \bot} \\
        \end{array}
    }
$$

$$
\frac
    {env \vartriangleright s \implies A \colon Set_t, \ \ A \not = \emptyset}
    {
        \begin{array}{l}
        {env \vartriangleright \texttt{Min}(s) \implies v \colon t, \ \ \forall x \in A \implies x > v} \\
        {env \vartriangleright \texttt{Max}(s) \implies v \colon t, \ \ \forall x \in A \implies v > x} \\
        \end{array}
    }
$$

$$
\frac
    {env \vartriangleright s \implies A \colon Set_{t_1}, \ \ env \vartriangleright e \implies f \colon t_1 \rightarrow t_2}
    {
        \begin{array}{l}
        {env \vartriangleright \texttt{Map}(e, s) \implies B \colon Set_{t_2}} \\
        {\forall a \in A \implies \left(\exists b \in B \mid b = f(a) \right)} \\
        {\forall b \in B \implies \left(\exists a \in A \mid b = f(a) \right)} \\
        \end{array}
    }
$$