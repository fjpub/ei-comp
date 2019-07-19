%% 
%% Copyright 2007-2019 Elsevier Ltd
%% 
%% This file is part of the 'Elsarticle Bundle'.
%% ---------------------------------------------
%% 
%% It may be distributed under the conditions of the LaTeX Project Public
%% License, either version 1.2 of this license or (at your option) any
%% later version.  The latest version of this license is in
%%    http://www.latex-project.org/lppl.txt
%% and version 1.2 or later is part of all distributions of LaTeX
%% version 1999/12/01 or later.
%% 
%% The list of all files belonging to the 'Elsarticle Bundle' is
%% given in the file `manifest.txt'.
%% 

%% Template article for Elsevier's document class `elsarticle'
%% with numbered style bibliographic references
%% SP 2008/03/01
%%
%% 
%%
%% $Id: elsarticle-template-num.tex 168 2019-02-25 07:15:41Z apu.v $
%%
%%
\documentclass[preprint,12pt]{elsarticle}

%% Use the option review to obtain double line spacing
%% \documentclass[authoryear,preprint,review,12pt]{elsarticle}

%% Use the options 1p,twocolumn; 3p; 3p,twocolumn; 5p; or 5p,twocolumn
%% for a journal layout:
%% \documentclass[final,1p,times]{elsarticle}
%% \documentclass[final,1p,times,twocolumn]{elsarticle}
%% \documentclass[final,3p,times]{elsarticle}
%% \documentclass[final,3p,times,twocolumn]{elsarticle}
%% \documentclass[final,5p,times]{elsarticle}
%% \documentclass[final,5p,times,twocolumn]{elsarticle}

%% For including figures, graphicx.sty has been loaded in
%% elsarticle.cls. If you prefer to use the old commands
%% please give \usepackage{epsfig}

%% The amssymb package provides various useful mathematical symbols
\usepackage{amssymb}
\usepackage{hyperref}
%% The amsthm package provides extended theorem environments
%% \usepackage{amsthm}

%% The lineno packages adds line numbers. Start line numbering with
%% \begin{linenumbers}, end it with \end{linenumbers}. Or switch it on
%% for the whole article with \linenumbers.
%% \usepackage{lineno}

\journal{Science of Computer Programming}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                        Begin of lts2TeX stuff                              %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%include lhs2TeX.fmt
%include lhs2TeX.sty
%include polycode.fmt

\usepackage{color}
\newcommand{\redFG}[1]{\textcolor[rgb]{0.6,0,0}{#1}}
\newcommand{\greenFG}[1]{\textcolor[rgb]{0,0.5,0}{#1}}
\newcommand{\blueFG}[1]{\textcolor[rgb]{0,0,0.8}{#1}}
\newcommand{\orangeFG}[1]{\textcolor[rgb]{0.8,0.4,0}{#1}}
\newcommand{\purpleFG}[1]{\textcolor[rgb]{0.4,0,0.4}{#1}}
\newcommand{\yellowFG}[1]{\textcolor[rgb]{0.8,0.33,0.0}{#1}}
\newcommand{\brownFG}[1]{\textcolor[rgb]{0.5,0.2,0.2}{#1}}
\newcommand{\blackFG}[1]{\textcolor[rgb]{0.06,0.06,0.06}{#1}}
\newcommand{\whiteFG}[1]{\textcolor[rgb]{1,1,1}{#1}}
\newcommand{\pinkFG}[1]{\textcolor[rgb]{1.0,0.0,0.5}{#1}}
\newcommand{\yellowBG}[1]{\colorbox[rgb]{1,1,0.2}{#1}}
\newcommand{\brownBG}[1]{\colorbox[rgb]{1.0,0.7,0.4}{#1}}

\newcommand{\ColourStuff}{
  \newcommand{\red}{\redFG}
  \newcommand{\green}{\greenFG}
  \newcommand{\blue}{\blueFG}
  \newcommand{\orange}{\orangeFG}
  \newcommand{\purple}{\purpleFG}
  \newcommand{\yellow}{\yellowFG}
  \newcommand{\brown}{\brownFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\whiteFG}
  \newcommand{\pink}{\pinkFG}
}

\newcommand{\MonochromeStuff}{
  \newcommand{\red}{\blackFG}
  \newcommand{\green}{\blackFG}
  \newcommand{\blue}{\blackFG}
  \newcommand{\orange}{\blackFG}
  \newcommand{\purple}{\blackFG}
  \newcommand{\yellow}{\blackFG}
  \newcommand{\brown}{\blackFG}
  \newcommand{\black}{\blackFG}
  \newcommand{\white}{\blackFG}
  \newcommand{\pink}{\blackFG}
}

\ColourStuff

\newcommand{\K}[1]{\yellow{\mathsf{#1}}}
\newcommand{\D}[1]{\blue{\mathsf{#1}}}
\newcommand{\Con}[1]{\green{\mathsf{#1}}}
\newcommand{\F}[1]{\blue{\mathsf{#1}}}
\newcommand{\V}[1]{\black{\mathsf{#1}}}
\newcommand{\N}[1]{\red{\mathsf{#1}}}
\newcommand{\JK}[1]{\purple{\mathsf{#1}}}
\newcommand{\RF}[1]{\pink{\mathsf{#1}}}
\newcommand{\Comm}[1]{\red{\textnormal{#1}}}

\DeclareMathAlphabet{\mathkw}{OT1}{cmss}{bx}{n}
%subst keyword a = "\mathkw{" a "}"
%subst conid a = "\V{" a "}"
%subst varid a = "\V{" a "}"
%subst numeral a = "\N{" a "}"
%subst comment a = "\footnotesize{\Comm{~\textit{-}\textit{-}~\textit{" a "}}}"

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                          End of lhs2Tex stuff                              %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\begin{frontmatter}

%% Title, authors and addresses

%% use the tnoteref command within \title for footnotes;
%% use the tnotetext command for theassociated footnote;
%% use the fnref command within \author or \address for footnotes;
%% use the fntext command for theassociated footnote;
%% use the corref command within \author for corresponding author footnotes;
%% use the cortext command for theassociated footnote;
%% use the ead command for the email address,
%% and the form \ead[url] for the home page:
%% \title{Title\tnoteref{label1}}
%% \tnotetext[label1]{}
%% \author{Name\corref{cor1}\fnref{label2}}
%% \ead{email address}
%% \ead[url]{home page}
%% \fntext[label2]{}
%% \cortext[cor1]{}
%% \address{Address\fnref{label3}}
%% \fntext[label3]{}

\title{Comparing Strategies on the Formalization of Modern Programming Languages in Agda}

%% use optional labels to link authors explicitly to addresses:
%% \author[label1,label2]{}
%% \address[label1]{}
%% \address[label2]{}

\author[ufpel]{Samuel Feitosa}
\author[utrecht]{Alejandro Serrano}
\author[ufop]{Rodrigo Ribeiro}
\author[ufpel]{Andre Du Bois}

\address[ufpel]{Programa de P\'os-Gradua\c{c}\~ao em Computa\c{c}\~ao, PPGC \\ Universidade Federal de Pelotas, Pelotas, RS - Brazil}
\address[utrecht]{Software Technology Group \\ Utrecht University, Utrecht, The Netherlands}
\address[ufop]{Programa de P\'os-Gradua\c{c}\~ao em Ci\^encia da Computa\c{c}\~ao, PPGCC \\ Universidade Federal de Ouro Preto, Ouro Preto, MG - Brazil}

\begin{abstract}
Nowadays, there are two main approaches to formalize and prove type safety for a programming language. In the first one, called extrinsic, usually, the syntax, typing, and evaluation rules are described separately, and the common theorems of progress and preservation link the rules to prove type safety. In the second one, called intrinsic, the syntax and the typing judgments are expressed as a single definition, thus allowing only the representation of well-typed terms, together with a terminating definitional interpreter modeling the evaluation guarantee type-safety. In this paper, we explore both approaches on the formalization of two well-known formal languages, $\lambda$-calculus and Featherweight Java, in the dependently-typed programming language Agda, comparing the subtleties of each approach, and showing that we can elaborate the extrinsic version into an intrinsic one.
\end{abstract}

%%Graphical abstract
%\begin{graphicalabstract}
%\includegraphics{grabs}
%\end{graphicalabstract}

%%Research highlights
%\begin{highlights}
%\item Research highlight 1
%\item Research highlight 2
%\end{highlights}

\begin{keyword}
Agda \sep Lambda Calculus \sep Featherweight Java
%% keywords here, in the form: keyword \sep keyword

%% PACS codes here, in the form: \PACS code \sep code

%% MSC codes here, in the form: \MSC code \sep code
%% or \MSC[2008] code \sep code (2000 is the default)
\end{keyword}

\end{frontmatter}

%% \linenumbers

%%%%%%%%%%%%%%%%%%%%%% Begin lhs2TeX definition %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%format data = "\K{data}"
%format where = "\K{where}"
%format with = "\K{with}"
%format . = "."
%format Set = "\D{Set}"
%format Set0 = Set "_{\D{0}}"
%format Set1 = Set "_{\D{1}}"
%format List = "\D{List}"
%format [] = "\Con{\lbrack\:\rbrack}"
%format , = "\red{,}\,"
%format Nat = "\D{\mathbb{N}}"
%format zero = "\Con{zero}"
%format succ = "\Con{suc}"
%format id = "\F{id}"
%format o = "\F{\circ}"
%format Vec = "\D{Vec}"
%format :: = "\Con{::}"
%format ∷ = "\Con{::}"
%format _::_ = "\Con{\_::\_}"

%%%%%%%%%%%%%%%%%%%% End of lhs2TeX definition %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%% main text
\section{Introduction}
\label{sec:intro}

Programming languages are applied in every computational problem, from simple applications, such as smartphone apps, to complex critical systems, like those for flight control. Thus, it is important to have mechanisms to ensure a programming language indeed implements certain behavior and enjoys some desired properties. We know that by using only tests, it is impossible to offer full guarantees, since tests can reach only a limited amount of cases. A research area concerned with proving these properties for every program is on the formalization of programming language semantics (or subset of it) in a proof assistant, such as Agda, Coq, or Isabelle, providing formal proofs that the language has the expected behavior. Mechanized proof assistants are powerful tools, however proof development can be difficult and time-consuming~\cite{Delaware:2011:PLT:2076021.2048113}. 

Today, the most used method for proving type-safety of a programming language is the syntactic approach (sometimes called extrinsic) proposed by Wright and Felleisen~\cite{Wright:1994:SAT:191905.191909}. Using this technique, the syntax is defined first, and then relations are defined to represent both the typing judgments (static semantics), and the evaluation through reduction steps (dynamic semantics). The common theorems of \emph{progress} and \emph{preservation} link the static and the dynamic semantics, guaranteeing that a well-typed term will not get stuck, i.e., it should be a value or be able to take another reduction step, preserving the intended type.

However, another technique is becoming increasingly popular in the recent years, which uses a functional approach (sometimes called intrinsic) to achieve a similar result, as proposed by Altenkirch and Reus~\cite{Altenkirch:1999:MPL:647849.737066}. The idea is to first encode the syntax and the typing judgments in a single definition which captures only well-typed expressions, usually within a total dependently-typed programming language. After that, one writes a definitional interpreter which evaluates the well-typed expressions. By using this approach, type-soundness is guaranteed by construction, and the necessary lemmas and proofs of the syntactic approach can be obtained (almost) for free.

In this context, this paper discusses the formalization and proofs of soundness of two languages, using both the extrinsic~\cite{Wright:1994:SAT:191905.191909} and intrinsic~\cite{Altenkirch:1999:MPL:647849.737066} representation of terms. The first, $\lambda$-calculus~\cite{Church32}, is a well-studied language within the functional programming community, used as basis to introduce the concepts regarding to both formalization approaches. The second, Featherweight Java~\cite{Igarashi:2001:FJM:503502.503505}, is a core calculus of a modern object-oriented language with a rigorous semantic definition of the main core aspects of Java. This work explores different techniques to prove type soundness of programming languages, and we show that it is possible to represent modern languages with complex structure and binding mechanisms using both styles of formalization. %Even though the case studies are interesting, and can be explored for future developments, we are aiming to argue that both techniques are equivalent, and according to the case, the programmers can choose the one that fits better for their domain.

\pagebreak

More concretely, we make the following contributions:

\begin{itemize}
\item We formalize the static and dynamic semantics of $\lambda$-calculus in both extrinsically and intrinsically-typed styles. We prove type soundness for the first using the common theorems of \emph{progress} and \emph{preservation}, and we implement a definitional interpreter for the second, which together with the intrinsic representation embeds the soundness proofs. 
\item We formalize the semantics of Featherweight Java, also considering both approaches. Similarly, we prove soundness for the extrinsic version by using the theorems of \emph{progress} and \emph{preservation}, and by using a definitional interpreter for the intrinsic version.
\item We present functions to \emph{elaborate} the extrinsic semantics to the intrinsic version, allowing the user to compare the results produced by each one. 
\item We discuss both approaches and their subtleties, using some metrics (such as lines of code, and number of lemmas and theorems) in order to provide a comparison between the formalization styles.
\end{itemize}

The remainder of this text is organized as follows: Section 2 gives an overview of the Agda language, and how it deals with dependent types. Section 3 presents the formalization of $\lambda$-calculus in the extrinsic and intrinsic styles, and the elaboration of the first into the second. Section 4 shows how we formalized (extrinsically and intrinsically) Featherweight Java, considering the modeling of class tables and its complex binding mechanism, also showing how to elaborate the extrinsic into the intrinsic version. Section 5 discusses and compares the different styles of formalization. Section 6 shows some related work. Finally, we present the final remarks in Section 7.

The languages presented in this paper have been formalized in Agda version 2.6.0 using Standard Library 1.0. We present here parts of the Agda code used in our definitions, not necessarily in a strict lexically-scoped order. Some formal proofs were omitted from the text to not distract the reader from understanding the high-level structure of the formalization. In such situations we give just proof sketches and point out where all details can be found in the source code. All source code produced, including the \LaTeX \ source of this paper, are available on-line~\cite{repos}.

\section{An Overview of Agda}
\label{sec:back}

%format String = "\D{String}"
%format Bool = "\D{Bool}"
%format forall = "\V{\forall}"
%format ℓ = "\V{\ell}"
%format ~Nr1~ = "\N{1}"
%format ~Nr2~ = "\N{2}"

Agda is a dependently-typed functional programming language based on Martin-L\"of intuitionistic type theory~\cite{Lof98}.  Function types and an infinite hierarchy of types of types, |Set ℓ|, where |ℓ| is a natural number, are built-in. Everything else is a user-defined type. The type |Set|, also known as |Set0|, is the type of all ``small'' types, such as |Bool|, |String| and |List Bool|.  The type |Set1| is the type of |Set| and ``others like it'', such as |Set -> Bool|, |String -> Set|, and |Set -> Set|. We have that |Set ℓ| is an element of the type |Set (ℓ + ~Nr1~)|, for every $\ell \geq 0$. This stratification of types is used to keep Agda consistent as a logical theory~\cite{Sorensen2006}.

An ordinary (non-dependent) function type is written |A -> B| and a dependent one is written |(x : A) -> B|, where type |B| depends on
|x|, or |forall (x : A) -> B|. Agda allows the definition of \emph{implicit parameters}, i.e.  parameters whose values can be infered from the context, by surrounding them in curly braces: |forall {x : A} -> B|. To avoid clutter, we omit implicit arguments from the source code presentation. The reader can safely assume that every free variable in a type is an implicity parameter.

As an example of Agda code, consider the following data type of length-indexed lists, also known as vectors.

\begin{code}
  data Nat : Set where
    zero : Nat
    succ : Nat -> Nat

  data Vec (A : Set) : Nat -> Set where
    []  : Vec A zero
    _::_ : forall {n} -> A -> Vec A n -> Vec A (succ n)
\end{code}

%format head = "\F{head}"

Constructor |[]| builds empty vectors. The cons-operator (|_::_|)\footnote{Agda supports the definition of mixfix operators. We can use underscores to mark arguments positions.} inserts a new element in front of a vector of $n$ elements (of type
|Vec A n|) and returns a value of type |Vec A (succ n)|. The |Vec| datatype is an example of a dependent type, i.e. a type that uses a value (that denotes its length). The usefulness of dependent types can be illustrated with the definition of a safe list head function: |head| can be defined to accept only non-empty vectors, i.e.~values of type |Vec A (succ n)|, which have at least one element.

\begin{spec}
  head : Vec A (succ n) -> A
  head (x :: xs) = x
\end{spec}

In |head|'s definition, the constructor |[]| is not used. The Agda type-checker can figure out, from |head|'s parameter type, that argument |[]| to |head| is not type-correct, hence we do not have to give a definition for that case.

%format _==_ = "\D{\_ \equiv \_}"
%format == = "\D{\equiv}"
%format refl = "\Con{refl}"
%format Fin   = "\D{Fin}"
%format lookup = "\F{lookup}"

Another useful data type is the finite type, which is defined in Agda's standard library as:

\begin{code}
  data Fin : Nat -> Set where
    zero : forall {n} -> Fin (succ n)
    succ : forall {n} -> Fin n -> Fin (succ n)
\end{code}
  
Note that Agda supports the overloading of data type constructor names. Constructor |zero| can refer to type |Nat| or |Fin|, depending on the context where the name is used. Type |Fin n| has exactly |n| inhabitants (elements), i.e. it is isomorphic to the set $\{0,...,n - 1\}$.
An application of such type is to define a safe vector lookup function, which avoids the access of invalid positions.

\begin{code}
  lookup : forall {A n} -> Fin n -> Vec A n -> A
  lookup zero (x :: _) = x
  lookup (succ idx) (_ :: xs) = lookup idx xs
\end{code}

Thanks to the propositions-as-types principle\footnote{Also known as Curry-Howard ``isomorphism''~\cite{Sorensen2006}.} we can interpret
types as logical formulas and terms as proofs. An example is the representation of equality as the following Agda type:

\begin{code}
  data _==_ forall {ℓ} {A : Set ℓ} (x : A) : A -> Set where
    refl : x == x
\end{code}

%format not = "\F{\neg}"
%format Dec = "\D{Dec}"
%format yes = "\Con{yes}"
%format no  = "\Con{no}"
%format Even = "\Con{Even}"
%format Odd = "\Con{Odd}"
%format Parity = "\D{Parity}"
%format parity = "\F{parity}"
%format natToBin = "\F{natToBin}"
%format false = "\Con{false}"
%format true = "\Con{true}"
%format + = "\F{+}"
%format ++ = "\F{++}"
%format Bot = "\D{\bot}"
%format All = "\D{All}"

This type is called propositional equality. It defines that there is a unique evidence for equality, constructor |refl| (for reflexivity),
that asserts that the only value equal to |x| is itself. Given a predicate |P : A -> Set| and a vector |xs|, the type |All P xs| is used to build proofs that |P| holds for all elements in |xs| and it is defined as:

\begin{spec}
  data All (P : A -> Set) : Vec A n ->  Set where
     [] : All P []
     _::_ : forall {x xs} -> P x -> All P xs -> All P (x :: xs)
\end{spec}
   
The first constructor specifies that |All P| holds for the empty vector and constructor |_::_| builds a proof of |All P (x :: xs)| from proofs of |P x| and |All P xs|. Since this type shares the structure with vectors, some functions on |Vec| have similar definitions for type |All|. As an example used in our formalization, consider the function |lookup|, which extracts a proof of |P| for the element at position |v :: Fin n| in a |Vec|:

\begin{spec}
   lookup : {xs : Vec A n} -> Fin n -> All P xs -> P x
   lookup zero (px :: _) = px
   lookup (succ idx) (_ :: pxs) = lookup idx pxs
\end{spec}

An important application of dependent types is to encode programming languages syntax. The role of dependent types in this domain is to encode programs that only allow well-typed and well-scoped terms~\cite{Benton2012} and to formally state their properties. Intuitively, we encode the static semantics of the object language in the host language AST's constructor, leaving the responsibility of checking type safety to the host's language type checker. As an example, consider the following simple expression language:

%format Expr = "\D{Expr}"
%format True = "\Con{True}"
%format False = "\Con{False}"
%format Num = "\Con{Num}"
%format _&_ = "\Con{\_\land\_}"
%format _+_ = "\Con{\_+\_}"

\begin{spec}
   data Expr : Set where
      True False : Expr
      Num : Nat -> Expr
      _&_ _+_ : Expr -> Expr -> Expr
\end{spec}
    
Using this data type we can construct expressions that denote terms that should not be considered well-typed like |(Num ~Nr1~) + True|. Using this approach, we need to specify the static semantics as another definition, which should consider all possible cases to avoid the definition of ill-typed terms.

Another possibility is to combine the static semantics and language syntax into a single definition, as shown below.

%format Ty = "\D{Ty}"
%format Natt = "\Con{Nat}"
%format Booll = "\Con{Bool}"

\begin{spec}
   data Ty : Set where
      Natt Booll : Ty

   data Expr : Ty -> Set where
      True False : Expr Booll
      Num : Natt -> Expr Natt
      _&_ : Expr Booll -> Expr Booll -> Expr Booll
      _+_ : Expr Natt -> Expr Natt -> Expr Natt
\end{spec}

In this definition, the |Expr| type is indexed by a value of type |Ty| which indicates the type of the expression being built. This way, Agda's type system can enforce that only well-typed terms could be written. A definition which uses the expression |(Num ~Nr1~) + True| will be rejected by Agda's type checker automatically.

For further information about Agda, see~\cite{Norell2009,Stump2016,Wadler-plfa}.

\section{Lambda Calculus}
\label{sec:lc}

The $\lambda$-calculus is a well-known purely functional core calculus proposed by Church in 1932~\cite{Church32} capable of expressing computation with only three syntactic constructors: variables, abstractions, and application. It is a universal model of computation equivalent to Turing machines. Roughly, this calculus consists of constructing lambda expressions and performing reductions operations on them, through function abstraction and application using variable binding and substitution~\cite{Wadler-plfa}.

In this paper we consider a variant of $\lambda$-calculus, called \emph{simply typed lambda-calculus} (STLC), which consists of the same base language augmented with some base types (or some other constructions). To keep this formalization as simple as possible, we added only the Boolean type. Throughout the next subsections we explain how we model the syntax and the semantics of STLC in Agda, and how we prove some basic properties of it, considering both formalization methods discussed earlier. This section is important to introduce some formalization concepts, which will be used in a more complex context in Section~\ref{sec:fj}.

\subsection{Extrinsic Formalization}

In this subsection, we follow the usual script for when extrinsically formalizing a programming language: first we give the syntax, the semantics and the typing rules, and then we prove the properties of progress and preservation. This text is highly based on what is presented on Wadler's~\cite{Wadler-plfa} and Pierce's~\cite{pierce2019software} books for the formalization of STLC in Agda and Coq, respectively. 

%format Var = "\Con{Var}"
%format Lam = "\Con{Lam}"
%format App = "\Con{App}"

\paragraph{Syntax definition}{As mentioned, we extended the STLC only with Boolean types. Thus, we have the three basic constructors of $\lambda$-calculus (|Var|, |Lam|, and |App|), and two constants representing the Boolean values |true| and |false|. In our definition, for simplicity, we represent a variable name as a natural number |Nat|. The next code shows how expressions are defined in Agda.}

\begin{spec}
data Expr : Set where
  true  : Expr
  false : Expr
  Var   : Nat -> Expr
  Lam   : Nat -> Expr -> Expr
  App   : Expr -> Expr -> Expr
\end{spec}

For example, the identity function is represented as |Lam ~Nr1~ (Var ~Nr1~)|. With this syntax we can create ill-scoped terms like |Lam ~Nr1~ (Var ~Nr2~)|, but our typing relation will forbid this.

% Is it important to discuss 'alpha renaming'?

%format Val = "\D{Val}"
%format V-True = "\Con{V\textrm{-}True}"
%format V-False = "\Con{V\textrm{-}False}"
%format V-Lam = "\Con{V\textrm{-}Lam}"
%format ∀ = "\V{\forall}"
%format → = "\rightarrow"

\paragraph{Values}{In our representation, besides the constants |true| and |false| being values, we also consider an \emph{abstraction} ($\lambda$-expression) a value, no matter whether the body expression is a value or not, i.e., reduction stops at abstractions. The reduction of a $\lambda$-expression only begins when a function is actually applied to an argument~\cite{pierce2019software}.}

\begin{spec}
data Val : Expr → Set where
  V-True  : Val true
  V-False : Val false
  V-Lam   : ∀ {x e} → Val (Lam x e)
\end{spec}

The inductive definition |Val| is indexed by an |Expr|, showing which syntactical constructor the value represents. The definition of values will be used next, during the formalization of the reduction steps.

%format _⟶_ = "\D{\_\longrightarrow\_}"
%format ⟶ = "\D{\longrightarrow}"
%format R-App₁ = "\Con{R\textrm{-}App_1}"
%format R-App₂ = "\Con{R\textrm{-}App_2}"
%format R-App = "\Con{R\textrm{-}App}"
%format e = "\V{e}"
%format e' = "\V{e''}"
%format e₁ = "\V{e_1}"
%format e₂ = "\V{e_2}"
%format e₁' = "\V{e_1''}"
%format e₂' = "\V{e_2''}"
%format v₁ = "\V{v_1}"
%format subs = "\D{subs}"
%format subst = "\D{subst}"

\paragraph{Dynamic semantics}{The present formalization considers the call-by-value evaluation strategy. The only reducible expression is the application |App| of a value to a $\lambda$-expression (represented by the constructor |Lam|). In the reduction relation |_⟶_| defined below, the rule |R-App₁| represents one step of evaluation to reduce the left-hand side of an application. This rule should be applied until the expression |e₁| becomes a value. Rule |R-App₂| is used when the left-hand side is already a value, and reduces the right-hand side of an application. Again, it should be applied until |e₂| becomes a value. After that, the rule |R-App| should be applied when both (left and right) expressions are values, and the left one is a |Lam|. With this setting, it applies a substitution (using function |subs|\footnote{We omit the implementation of function |subs|, however it is available online~\cite{repos}.}) of the actual parameter |v₁| where the formal parameter |x| appears in the body expression |e|.}

\begin{spec}
subs : Expr → Nat → Expr → Expr
-- Implementation omitted

data _⟶_ : Expr → Expr → Set where
  R-App₁ : ∀ {e₁ e₂ e₁'}
        → e₁ ⟶ e₁'
        → App e₁ e₂ ⟶ App e₁' e₂
  R-App₂ : ∀ {v₁ e₂ e₂'}
        → Val v₁
        → e₂ ⟶ e₂'
        → App v₁ e₂ ⟶ App v₁ e₂'
  R-App  : ∀ {x e v₁}
        → Val v₁
        → App (Lam x e) v₁ ⟶ (subs e x v₁)
\end{spec}

%format bool = "\Con{bool}"
%format _⇒_ = "\Con{\_\Longrightarrow\_}"
%format ⇒ = "\Con{\Longrightarrow}"

\paragraph{Syntax of types}{In the presented formalization, there are only two types: |bool| represents Booleans, and |_⇒_| represents a \emph{function type}. The function type represents the type for a $\lambda$-expression using two arguments. The first represents the expected parameter type, and the second represents the return type of a given $\lambda$-expression.}

\begin{spec}
data Ty : Set where
  bool : Ty
  _⇒_ : Ty → Ty → Ty
\end{spec}
      
%format T-True = "\Con{T\textrm{-}True}"
%format T-False = "\Con{T\textrm{-}False}"
%format T-Var = "\Con{T\textrm{-}Var}"
%format T-Lam = "\Con{T\textrm{-}Lam}"
%format T-App = "\Con{T\textrm{-}App}"
%format _⊢_∶_ = "\D{\_\vdash\_:\_}"
%format _∋_∶_ = "\D{\_\ni\_:\_}"
%format ⊢ = "\D{\vdash}"
%format ∶ = "\D{:}"
%format ∋ = "\D{\ni}"
%format Ctx = "\D{Ctx}"
%format Γ = "\V{\Gamma}"
%format τ = "\V{\tau}"
%format τ₁ = "\V{\tau_1}"
%format τ₂ = "\V{\tau_2}"
%format ℕ = "\D{\mathbb{N}}"
%format × = "\D{\times}"

\paragraph{Expression typing}{The |_⊢_∶_| relation encodes the typing rules of STLC, indicating that considering a context |Ctx|, an expression |Expr| has type |Ty|. A context |Ctx| is defined as a list of pairs |List (ℕ × Ty)|, linking each variable with its given type. The first two rules are simple: constants |true| and |false| have always type |bool| no matter what is contained in a context |Γ|. Rule |T-Var| uses an auxiliary definition for context lookup |_∋_∶_|\footnote{We also omit the definition of \emph{context lookup}, but it can be found in our repository~\cite{repos}.} which binds a type |τ| for a variable |x| according to a context |Γ|. Rule |T-Lam| uses our typing judgment to type the right-hand side of a $\lambda$-expression with a context |Γ| extended with the formal parameter (left-hand side) of that $\lambda$-expression. We use the list concatenation |(x , τ₁) ∷ Γ| to extend the context, and the result is a function type |τ₁ ⇒ τ₂|. The last rule |T-App| guarantees the correct type for expressions |e₁| and |e₂| to perform an application. The first (|e₁|) should have a function type |(τ₁ ⇒ τ₂)|, and the second (|e₂|) should be of type |τ₁|, assuring that the formal and actual parameters are of the same type. If both premises hold, the typing judgment results in |τ₂|, which is the return type of the $\lambda$-expression.}

\begin{spec}
data _⊢_∶_ : Ctx → Expr → Ty → Set where
  T-True  : ∀ {Γ}
         → Γ ⊢ true ∶ bool
  T-False : ∀ {Γ}
         → Γ ⊢ false ∶ bool
  T-Var   : ∀ {Γ x τ}
         → Γ ∋ x ∶ τ
         → Γ ⊢ (Var x) ∶ τ
  T-Lam   : ∀ {Γ x e τ₁ τ₂}
         → ((x , τ₁) ∷ Γ) ⊢ e ∶ τ₂
         → Γ ⊢ (Lam x e) ∶ (τ₁ ⇒ τ₂)
  T-App   : ∀ {Γ e₁ e₂ τ₁ τ₂}
         → Γ ⊢ e₁ ∶ (τ₁ ⇒ τ₂)
         → Γ ⊢ e₂ ∶ τ₁
         → Γ ⊢ (App e₁ e₂) ∶ τ₂
\end{spec}

%format preservation = "\D{preservation}"
%format r₁ = "\V{r_1}"
%format r₂ = "\V{r_2}"

\paragraph{Soundness proofs}{We formalized the common theorems of \emph{progress} and \emph{preservation} for the presented calculus in Agda. Since STLC is a small calculus, the proofs are carried simply by induction in the structure of the typing judgment.}

The |preservation| function represents the theorem with the same name, stating that if a well-typed expression |e| has type |τ| in an empty context |[]|, and it takes a reduction step |e ⟶ e'|, then |e'| remains with type |τ|. The only typing rule that matters is the one that applies one expression to another, with three cases, one for each reduction rule: the first applies the induction hypothesis to the left-side expression, the second is similar, but applies the induction hypothesis to the right-side, and the last one uses an auxiliary function |subst| representing the lemma which states that \emph{Substitution Preserves Typing}\footnote{For brevity, we present only the type of |subst| here, but the complete proof (and its related lemmas) can be found in our source-code repository~\cite{repos}}. All the other cases represent values (impossible cases), which cannot take any reduction step.

\begin{spec}
subst : [] ⊢ v ∶ τ₁ → (x , τ₁) ∷ Γ ⊢ e ∶ τ₂ → Γ ⊢ (subs e x v) ∶ τ₂
-- Proof code omitted
  
preservation : ∀ {e e' τ} → [] ⊢ e ∶ τ → e ⟶ e' → [] ⊢ e' ∶ τ
preservation T-True ()
preservation T-False ()
preservation (T-Var ()) 
preservation (T-Lam _) ()
preservation (T-App r₁ r₂) (R-App₁ s) = T-App (preservation r₁ s) r₂
preservation (T-App r₁ r₂) (R-App₂ v₁ s) = T-App r₁ (preservation r₂ s)
preservation (T-App (T-Lam r₁) r₂) (R-App v₁) = subst r₂ r₁
\end{spec}

%format progress = "\D{progress}"
%format canonical = "\D{canonical}"
%format Progress = "\D{Progress}"
%format Canonical = "\D{Canonical}"
%format Done = "\D{Done}"
%format Step = "\D{Step}"
%format C-Lam = "\Con{C\textrm{-}Lam}"
%format C-True = "\Con{C\textrm{-}True}"
%format C-False = "\Con{C\textrm{-}False}"

Similarly to the previous theorem, the |progress| function represents the theorem with the same name, stating that if a well-typed expression |e| has type |τ| in an empty context |[]|, then it can make \emph{Progress}, i.e., or |e| is a value, or it can take another reduction step. First we define an inductive datatype to hold the result of our proof, with two constructors: |Done| when |e| is a value, and |Step| when |e| reduces to an |e'|. 

\begin{spec}
data Progress (e : Expr) : Set where
  Step : ∀ {e'}
      → e ⟶ e'
      → Progress e
  Done : Val e
      → Progress e
\end{spec}

We also need to establish a basic property of reduction and types, identifying the possible \emph{canonical forms} (i.e., well-typed closed values) belonging to each type~\cite{pierce2019software}. The definition has one constructor for each value (|C-True|, |C-False|, and |C-Lam|), and its proof linking each value with its respective type\footnote{We show only the type definition for |Canonical| and |canonical|. The complete source code is available online~\cite{repos}.}.

\begin{spec}
data Canonical : Expr → Ty → Set where
-- Inductive definition code omitted  
canonical : ∀ {v τ} → [] ⊢ v ∶ τ → Val v → Canonical v τ
-- Proof code omitted
\end{spec}

The proof for \emph{progress} is straightforward: cases with values are finished with |Done| and the respective |Val| constructor; and the case dealing with application is finished with |Step|, using the induction hypothesis for the left and right side, and the canonical form |C-Lam|, which relates the values with their types. 

\begin{spec}
progress : ∀ {e τ} → [] ⊢ e ∶ τ → Progress e
progress T-True = Done V-True
progress T-False = Done V-False
progress (T-Var ())
progress (T-Lam _) = Done V-Lam
progress (T-App e₁ e₂) with progress e₁
... | Step stp₁ = Step (R-App₁ stp₁)
... | Done v₁ with progress e₂
...   | Step stp₂ = Step (R-App₂ v₁ stp₂)
...   | Done v₂ with canonical e₁ v₁
...     | C-Lam stp = Step (R-App v₂)
\end{spec}

\subsection{Intrinsic Formalization}

This subsection introduces the intrinsically-typed formalization, and the implementation of a definitional interpreter for the STLC. This text should serve as basis to understand the basics of this approach, considering how we use dependent-types to encode the syntax and typing rules, and how we use \emph{de Bruijn} indices~\cite{DEBRUIJN1972381} to deal with name binding. Again, the concepts presented here will be used in a more complex environment when formalizing Featherweight Java.

%format σ = "\V{\sigma}"
%format ∷ = "\Con{::}"
%format _∈_ = "\D{\_\in\_}"
%format ∈ = "\D{\in}"

\paragraph{Intrinsically-typed syntax}{Representing the typing rules combined with the language syntax is a well-known approach~\cite{Altenkirch:1999:MPL:647849.737066,Reynolds01whatdo}. Using such approach, only well-typed expressions are accepted by the host language (Agda in our case), and ill-typed expressions are rejected by the compiler accusing type error. Using this approach the defined abstract syntax trees (ASTs) not only capture the syntactic properties of the language but semantic properties as well. We highlight the importance of the approach here because it allows programmers to reason about their programs as they write them rather than separately at the meta-logical level.}

Since we are embedding types together with the syntax, we need a |Ty|, which is the same presented in the previous section, and a type context |Ctx|, which is represented by a |List Ty|. Then, the expression definition is parameterized by a |Γ| of type |Ctx|, which binds a type for each free variable, and indexed by a |Ty|, which represents the type of a given expression. The following code show our |Expr| definition.

\begin{spec}
data Expr (Γ : Ctx) : Ty → Set where
  true  : Expr Γ bool
  false : Expr Γ bool
  Var   : ∀ {x} → x ∈ Γ → Expr Γ x
  Lam   : ∀ σ {τ} → Expr (σ ∷ Γ) τ  → Expr Γ (σ ⇒ τ)
  App   : ∀ {σ τ} → Expr Γ (σ ⇒ τ) → Expr Γ σ → Expr Γ τ
\end{spec}

The first two constructors represent the constants |true| and |false|, both with type |bool|. The constructor |Var| shows us a different way to represent variables. All name bindings are done with statically-checked \emph{de Bruijn} indices~\cite{DEBRUIJN1972381}, a technique for handling binding by using a nameless, position-dependent name scheme. Thus, with this constructor, we do not use a name to identity a variable, but a well-typed \emph{de Bruijn} index |x ∈ Γ| which witnesses the existence of an element |x| in |Γ|, as defined by the standard library |_∈_| operator. The result type of this expression should be the one represented by the x variable type. This technique is well known for avoiding out-of-bound errors. The |Lam| constructor expects a |σ| of type |Ty|, representing the formal parameter of a $\lambda$-expression, and an expression |Expr (σ ∷ Γ) τ|, representing its body. Here we note that the expected expression has type |τ| considering an extended context |σ ∷ Γ|. Then, the resulting type for this expression is of a function type |σ ⇒ τ|. The last constructor |App| expects two expressions, the first with a function type |σ ⇒ τ|, and the second with a type |σ|, which has the same type of the formal parameter of the first expression. If both expressions respect the premises, an expression of type |τ| is constructed.

%format Value = "\D{Value}"
%format Env = "\D{Env}"

\paragraph{Values and Environments}{To define the STLC interpreter, we need intrinsically-typed values and environments. First we define a |Value| indexed by a type |Ty|. By using this definition, when interpreting the code, we are able to convert the result to an Agda type (host language semantics). So, if the value represents a |bool|, it results in the Agda's |Bool| type. In the case of a function type, it results in an Agda's function type.}

\begin{spec}
Value : Ty → Set
Value bool = Bool
Value (σ ⇒ τ) = Value (σ) → Value (τ)
\end{spec}

When working with such intrinsically-typed definition, an environment holds the information for which |Value| is associated with each variable in the context |Γ|. The representation of this environment is not totally obvious, since variables can have different types~\cite{Augustsson99anexercise}. We encoded it by using the datatype |All|, where each type in the context is linked with a typed value, as we can see next.

\begin{spec}
Env : Ctx → Set
Env Γ = All Value Γ
\end{spec}

%format eval = "\D{eval}"
%format lookup = "\D{lookup}"
%format λ = "\lambda"

\paragraph{Definitional interpreter}{We present next a fairly standard definition of an interpreter for STLC in Agda. The interpreter has three main points: processing of primitive values, variable lookup, and performing the actual evaluation of a $\lambda$-expression. The function |eval| pattern matches on the given |Expr|, dealing with each case, as follows.}

\begin{spec}
eval : ∀ {Γ τ} → Env Γ → Expr Γ τ → Value τ
eval env true = true
eval env false = false
eval env (Var x) = lookup env x
eval env (Lam σ e) = λ x → (eval (x ∷ env) e)
eval env (App e e₁) = eval env e (eval env e₁)
\end{spec}

The cases for |true| and |false| are simple. The case for |Var| uses the standard library's function |lookup| to project the appropriate value from the run-time environment |env|. The typed \emph{de Bruijn} index guarantees that the value projected from the environment has the type demanded since the environment is typed by the context |Γ|, which allows us to look up values of a particular type |x| in an environment |Env Γ| using the witness |x ∈ Γ|.

The case for |Lam| is tricky. It converts our definition to a $\lambda$-expression in Agda. The case for |App| evaluates the first expression |e|, which results in a $\lambda$-expression, and applies to it the result of evaluating the second expression |e₁|. We can note that we are delegating to Agda the actual evaluation of expressions, so we do not have to define substitution as in the extrinsic formalization.

There are two points to highlight with the presented approach. First, we can note that we do not have any error treatment in our interpreter. This is happening because we are working only with a (intrinsically) well-typed term, so in this case, every time a variable is requested it is guaranteed by construction that it exists with the correct type. The same happens when applying one expression to another. The well-typed syntax guarantees that the first expression is indeed a $\lambda$-expression (produced by our |Lam| case) and the second expression has the correct type.

Second, by allowing only the representation of well-typed expressions, the \emph{preservation} property is also assured by construction, and by writing such evaluator in a total language like Agda, the \emph{progress} property is guaranteed by consequence.

\subsection{Elaborating Extrinsic STLC to Intrinsic}

%format elab = "\D{elab}"
%format elab-var = "\D{elab\textrm{-}var}"
%format p₁ = "\V{p_1}"

We show, by using the |elab| function, that we can elaborate an extrinsic well-typed expression (using our extrinsic typing predicate |Γ ⊢ e ∶ τ|) to an intrinsic expression, which is well-typed by construction. The first two cases are straightforward, returning the Boolean expression associated with each constructor. The case |T-Var| results in a intrinsic |Var|, and the function |elab-var| (omitted here) produces a \emph{de Bruijn} index according to its position on the environment. The case for |T-Lam| results a |Lam| expression, elaborating its body recursively. Similarly, |T-App| results in an |App| expression, elaborating both (left and right) expressions recursively.

\begin{spec}
elab : ∀ {Γ e τ} → Γ ⊢ e ∶ τ → Expr Γ τ
elab T-True = true
elab T-False = false
elab (T-Var x) = Var (elab-var x)
elab (T-Lam {x = x} p) = Lam x (elab p)
elab (T-App p p₁) = App (elab p) (elab p₁)
\end{spec}

% Improve this paragraph

One can use this elaboration function to check that both semantic approaches produce the same result.

\section{Featherweight Java}
\label{sec:fj}

Featherweight Java (FJ)~\cite{Igarashi:2001:FJM:503502.503505} is a minimal core calculus for Java, in the sense that as many features of Java as possible are omitted, while maintaining the essential flavor of the language and its type system. FJ is to Java what $\lambda$-calculus is to Haskell. It offers similar operations, providing classes, methods, attributes, inheritance and dynamic casts with semantics close to Java's. The Featherweight Java project favors simplicity over expressivity and offers only five ways to create terms: object creation, method invocation, attribute access, casting and variables~\cite{Igarashi:2001:FJM:503502.503505}. This fragment is large enough to include many useful programs.

%format JClA = "\Con{A}"
%format JClB = "\Con{B}"
%format JClPair = "\Con{Pair}"
%format JClObj = "\Con{Object}"
%format JCA = "\D{A}"
%format JCB = "\D{B}"
%format JCPair = "\D{Pair}"
%format setfst = "\D{setfst}"
%format class = "\JK{class}"
%format extends = "\JK{extends}"
%format super = "\JK{super}"
%format this = "\JK{this}"
%format new = "\JK{new}"
%format return = "\JK{return}"
%format this.fst=fst = "\JK{this}\V{.fst=fst}"
%format this.snd=snd = "\JK{this}\V{.snd=snd}"
%format this.snd = "\JK{this}\V{.snd}"
%format , = "\V{,}"

A program in FJ consists of the declaration of a set of classes and an expression to be evaluated, which corresponds to Java's main method. The following example shows how classes can be modeled in FJ. There are three classes, |JClA|, |JClB|, and |JClPair|, with constructor and method declarations.

\begin{spec}
class JClA extends JClObj {
  JCA() { super(); }
}
class JClB extends JClObj {
  JCB() { super(); }
}
class JClPair extends JClObj {
  JClObj fst; 
  JClObj snd;
  JCPair(JClObj fst, JClObj snd) {
    super(); 
    this.fst=fst;
    this.snd=snd;
  }
  JClPair setfst(JClObj newfst) {
    return new JClPair(newfst, this.snd);
  }
}
\end{spec}

In the following example we can see two different kinds of expressions: |new JClA|(), |new JClB|(), and |new JClPair|(...) are \emph{object constructors}, and .|setfst|(...) refers to a \emph{method invocation}. 

\begin{spec}
new JClPair(new JClA(), new JClB()) . setfst(new JClB());
\end{spec}

FJ semantics provides a purely functional view without side effects. In other words, attributes in memory are not affected by object operations~\cite{Pierce:2002:TPL:509043}. Furthermore, interfaces, overloading, call to base class methods, null pointers, base types, abstract methods, statements, access control, and exceptions are not present in the language~\cite{Igarashi:2001:FJM:503502.503505}. As the language does not allow side effects, it is possible to formalize the evaluation directly on FJ terms, without the need for auxiliary mechanisms to model the heap~\cite{Pierce:2002:TPL:509043}. 

This calculus is intended to be a starting point for the study of various operational features of object-oriented programming in Java-like languages, being compact enough to make rigorous proofs feasible. Besides the rules for evaluation and type-checking,
Igarashi et al.~\cite{Igarashi:2001:FJM:503502.503505} present (paper) proofs of type soundness for FJ.

\subsection{Extrinsic Formalization}

This subsection presents our formalization of a large subset of FJ in Agda using the usual syntactic approach. As for STLC, this encoding was also divided in two major parts. First a set of definitions corresponding to the syntax, auxiliary functions, reduction and typing rules was created, followed by the main proofs for type soundness of the encoded language.

%format record = "\K{record}"
%format field = "\K{field}"
%format Class = "\D{Class}"
%format Meth = "\D{Meth}"
%format Name = "\D{Name}"
%format Field = "\Con{Field}"
%format Invk = "\Con{Invk}"
%format New = "\Con{New}"
%format cname = "\RF{cname}"
%format ext = "\RF{ext}"
%format flds = "\RF{flds}"
%format meths = "\RF{meths}"
%format ret = "\RF{ret}"
%format params = "\RF{params}"
%format body = "\RF{body}"

\paragraph{Syntax}{The definition of FJ is more intricate than STLC. An expression can refer to information of two sources: (1) a context to deal with variables, similar to STLC; (2) a class table, which stores information about all classes in the source-code program. Besides, there is a mutual relation between classes and expressions: an expression can refer to information about classes, and a class can contain expressions (which represent the method body).}

Considering all this, we start our formalization in Agda by defining the syntactic elements regarding FJ. A |Class| is represented by a record with three fields. The class name is stored in |cname|, the attributes are in |flds|, and the methods are in |meths|. For simplicity, we represent all the names as natural numbers (|Name = ℕ|).

\begin{spec}
record Class : Set where
  field
    cname  : Name
    flds   : List (Name × Name)
    meths  : List (Name × Meth)
\end{spec}

As we can see, attributes are represented by a |List| of tuples |(Name × Name)|, encoding the name and the type for each field. For methods, we have a similar setting, however, we use a |List| of tuples |(Name × Meth)|, where the first element is the method name, and the second encodes the method information, containing the return type |ret|, the method parameters |params|, and the method body |body|, as we can see below:

\begin{spec}
record Meth : Set where
  field
    ret     : Name
    params  : List (Name × Name)
    body    : Expr
\end{spec}

An expression can appear in two parts of a FJ program. It can appear in a method body, or it can represent the Java's main method, acting as a starting point for the program. We represent it using an inductive definition, considering the following constructors.

\begin{spec}
data Expr : Set where
  Var    : Name → Expr
  Field  : Expr → Name → Expr
  Invk   : Expr → Name → List Expr → Expr
  New    : Name → List Expr → Expr
\end{spec}

A variable is represented by the constructor |Var|, a field access is encoded by |Field|, a method invocation by |Invk|, and object instantiation is defined by |New|~\cite{Igarashi:2001:FJM:503502.503505}.

The only possible value in FJ is encoded in the |Val| definition. Since Java adopts a call-by-value evaluation strategy, to be a value, we need an object instantiation with all parameters being values themselves. This was encoded using the standard library's datatype |All|. 

%format V-New = "\Con{V\textrm{-}New}"

\begin{spec}
data Val : Expr → Set where
  V-New : ∀ {c cp} → All Val cp → Val (New c cp)
\end{spec}

%format fields = "\D{fields}"
%format method = "\D{method}"
%format Obj = "\D{Obj}"
%format ct = "\D{ct}"
%format Δ = "\V{\Delta}"
%format obj = "\Con{obj}"
%format other = "\Con{other}"
%format this = "\Con{this}"
%format Class.flds = "\RF{Class.flds}"
%format Class.meths = "\RF{Class.meths}"

\paragraph{Auxiliary definitions}{A FJ expression can refer to information present on the class table, where all classes of a given program are stored. To reason about information of a given class, we defined two auxiliary definitions. Using the definition |fields| one can refer to information about the attributes of a class.

\begin{spec}
data fields : Name → List (Name × Name) → Set where
  obj    : fields Obj []
  other  : ∀ {c cd}
         → Δ ∋ c ∶ cd
         → fields c (Class.flds cd)
\end{spec}

Similarly to STLC, we also use a predicate to lookup in a given list of pairs (|_∋_∶_|)\footnote{We omit the code of |_∋_∶_| predicate, but it can be found in our repository~\cite{repos}.}. In FJ we use this definition to lookup for classes, fields, methods, and variables.

By using the predicate |method| it is possible to refer information about a specific method in a certain class. Both auxiliary definitions refer to information on a class table |Δ|, which is defined globally in the working module.

\begin{spec}
data method : Name → Name → Meth → Set where
  this : ∀ {c cd m mdecl}
       → Δ ∋ c ∶ cd
       → (Class.meths cd) ∋ m ∶ mdecl
       → method c m mdecl 
\end{spec}

%format R-Field = "\Con{R\textrm{-}Field}"
%format RC-Field = "\Con{RC\textrm{-}Field}"
%format R-Invk = "\Con{R\textrm{-}Invk}"
%format RC-InvkRecv = "\Con{RC\textrm{-}InvkRecv}"
%format RC-InvkArg = "\Con{RC\textrm{-}InvkArg}"
%format RC-NewArg = "\Con{RC\textrm{-}NewArg}"
%format flds = "\V{flds}"
%format interl = "\D{interl}"
%format Meth.params = "\RF{Meth.params}"
%format Meth.body = "\RF{Meth.body}"
%format ↦ = "\D{\longmapsto}"

\paragraph{Reduction rules}{The reduction predicate takes two expressions as arguments. The predicate holds when expression |e| reduces to some expression |e'|. The evaluation relation is defined with the following type.}

\begin{spec}
data _⟶_ : Expr → Expr → Set 
\end{spec}

When encoding the reduction relation, we use two important definitions\footnote{Both definitions can be found online~\cite{repos}.}: |interl|, which is an inductive definition to interleave the information of a list of pairs (|List (Name × A)|) with a |List B|, providing a new list |List (Name × B)|; and |subs|, which is responsible to apply the substitution of a parameter list into a method body. We present only their types next.

\begin{spec}
data interl : List (Name × A) → List B → List (Name × B) → Set
-- Inductive definition code omitted.  
subs : Expr → List (Name × Expr) → Expr
-- Function code omitted.
\end{spec}

From now on we explain each constructor of the evaluation relation separately to make it easier for the reader.

Constructor |R-Field| encodes the behavior when accessing a field of a given class. All fields of a class are obtained using |fields C flds|. We interleave the definition of fields |flds| with the list of expressions |cp| received as parameters for the object constructor by using |interl flds cp fes|. With this information, we use |fes ∋ f ∶ fi| to bind the expression |fi| related to field |f|.

\begin{spec}
  R-Field : ∀ {C cp flds f fi fes}
             → fields C flds
             → interl flds cp fes
             → fes ∋ f ∶ fi
             → Field (New C cp) f ⟶ fi
\end{spec}

Constructor |R-Invk| represents the encoding to reduce a method invocation. We use |method C m MD| to obtain the information about method |m| on class |C|. As in |R-Field| we interleave the information about the method parameters |Meth.params MD| with a list of expressions |ap| received as the actual parameters on the current method invocation. Then, we use the function |subs| to apply substitution of the parameters in the method body.

\begin{spec}
  R-Invk : ∀ {C cp m MD ap ep}
             → method C m MD
             → interl (Meth.params MD) ap ep
             → Invk (New C cp) m ap ⟶ subs (Meth.body MD) ep
\end{spec}

%format _↦_ = "\D{\_\longmapsto\_}"

All the next constructors represent the congruence rules of the FJ calculus. Reduction of the first expression |e| is done by |RC-Field| and |RC-InvkRecv|, producing an |e'|.

\begin{spec}
  RC-Field : ∀ {e e' f}
             → e ⟶ e'
             → Field e f ⟶ Field e' f
  RC-InvkRecv : ∀ {e e' m mp}
             → e ⟶ e'
             → Invk e m mp ⟶ Invk e' m mp
\end{spec}

Reduction of arguments when invoking a method or instantiating an object is done by |RC-InvkArg| and |RC-NewArg|. We use an extra predicate (|_↦_|) to evaluate a list of expressions recursively. 
           
\begin{spec}               
  RC-InvkArg : ∀ {e m mp mp'}
             → mp ↦ mp'
             → Invk e m mp ⟶ Invk e m mp'
  RC-NewArg : ∀ {C cp cp'}
             → cp ↦ cp'
             → New C cp ⟶ New C cp'
\end{spec}

%format T-Field = "\Con{T\textrm{-}Field}"
%format T-Invk = "\Con{T\textrm{-}Invk}"
%format T-New = "\Con{T\textrm{-}New}"
%format Meth.ret = "\RF{Meth.ret}"
%format proj₁ = "\RF{proj_1}"
%format proj₂ = "\RF{proj_2}"
%format unzip = "\D{unzip}"
%format ⊧ = "\D{\models}"
%format _⊧_∶_ = "\D{\_\models\_:\_}"

\paragraph{Typing rules}{The typing rules for FJ are divided in two main parts: there are two predicates to type an expression, and two predicates to check if classes and methods are well-formed. A FJ program is well-typed if all typing predicates hold for a given program.}

To type an expression, we have the typing judgment predicate |_⊢_∶_| which encodes the typing rules of FJ, and the predicate |_⊧_∶_| responsible to apply the typing judgment |_⊢_∶_| to a list of expressions. Next we show their type definitions.

\begin{spec}
data _⊢_∶_  : Ctx → Expr → Name → Set
data _⊧_∶_  : Ctx → List Expr → List Name → Set  
\end{spec}

Both definitions are similar, receiving three parameters each. The first parameter is a type context |Ctx|, similar to the one for $\lambda$-calculus, aiming to store the types for variables. The second is represented by an |Expr| for the typing judgment, and a |List Expr| for the recursive case, both representing the expressions being typed. The last argument is a |Name| (or |List Name|) representing the types for the given expressions. Next we present each constructor for the |_⊢_∶_| predicate.

The constructor |T-Var| is similar to the one presented for $\lambda$-calculus. A variable |x| has type |C| if this variable is present in a context |Γ| with its type.

\begin{spec}
  T-Var : ∀ {Γ x C}
         → Γ ∋ x ∶ C
         → Γ ⊢ (Var x) ∶ C
\end{spec}

Constructor |T-Field| is more elaborated. First, we use the typing judgment to obtain the type of the sub-expression |e|. Then, we use the auxiliary definition |fields| which gives us the attributes |flds| of a class |C|. Likewise variables, the type of |f| is obtained by the information stored in |flds|.

\pagebreak

\begin{spec}
  T-Field : ∀ {Γ C Ci e f flds}
         → Γ ⊢ e ∶ C
         → fields C flds
         → flds ∋ f ∶ Ci
         → Γ ⊢ (Field e f) ∶ Ci
\end{spec}

Constructor |T-Invk| also uses the typing judgment to obtain the type for the sub-expression |e|. After that, we use our auxiliary predicate |method| to obtain the definition of method |m| in class |C|. It is used to type-check the method parameters |mp|\footnote{We use |proj₂| to get the second argument of a tuple, and |unzip| to split a list of tuples.}. Considering that all the premises hold, the type of a method invocation is given by |Meth.ret MD|.

\begin{spec}
  T-Invk : ∀ {Γ C e m MD mp}
         → Γ ⊢ e ∶ C
         → method C m MD
         → Γ ⊧ mp ∶ proj₂ (unzip (Meth.params MD))
         → Γ ⊢ (Invk e m mp) ∶ (Meth.ret MD)
\end{spec}

Similarly to |T-Invk|, in the definition |T-New| we also use the predicate to type a list of expressions. In this case, the premises will hold if the actual parameters |cp| of the class constructor are respecting the expected types for the |fields| of a given class |C|. 

\begin{spec}
  T-New : ∀ {Γ C cp flds}
         → fields C flds
         → Γ ⊧ cp ∶ proj₂ (unzip flds)
         → Γ ⊢ (New C cp) ∶ C
\end{spec}

%format ClassOk = "\D{ClassOk}"
%format MethodOk = "\D{MethodOk}"
%format T-Class = "\Con{T\textrm{-}Class}"
%format T-Method = "\Con{T\textrm{-}Method}"

A class is well-formed if it respects the |ClassOk| predicate. In our definition, we use the |All| datatype to check if all methods are correctly typed.

\begin{spec}
data ClassOk : Class → Set where
  T-Class : ∀ {CD}
         → All (MethodOk CD) (proj₂ (unzip (Class.meths CD)))
         → ClassOk CD
\end{spec}

Similarly, a method is well-formed in a class if it respects the |MethodOk| predicate. We use the expression typing judgment as a premise to type-check the expression body using the formal parameters as the environment |Γ|, expecting the type defined as the return type of the given method.

\begin{spec}
data MethodOk : Class → Method → Set where
  T-Method : ∀ {CD MD}
          → Meth.params MD ⊢ Meth.body MD ∶ Meth.ret MD
          → MethodOk CD MD
\end{spec}

%format rewrite = "\K{rewrite}"
%format ⊢-interl = "\D{\vdash\hspace{-3pt}\textrm{-}interl}"
%format ⊧-interl = "\D{\models\hspace{-3pt}\textrm{-}interl}"
%format ∋-interl = "\D{\ni\hspace{-3pt}\textrm{-}interl}"
%format ⊢-method = "\D{\vdash\hspace{-3pt}\textrm{-}method}"
%format ≡-fields = "\D{\equiv\hspace{-3pt}\textrm{-}fields}"
%format ≡-method = "\D{\equiv\hspace{-3pt}\textrm{-}method}"
%format progress-list = "\D{progress\textrm{-}list}"
%format preservation-list = "\D{preservation\textrm{-}list}"
%format fs₁ = "\V{fs_1}"
%format fs₂ = "\V{fs_2}"
%format fs₃ = "\V{fs_3}"

\paragraph{Properties}{We proved type soundness through the standard theorems of \emph{preservation} and \emph{progress} for our formalization of FJ.}

The function |preservation| is the Agda encoding for the theorem with the same name, stating that if we have a well-typed expression, it preserves type after taking a reduction step. The proof proceeds by induction on the typing derivation of the first expression. 

\begin{spec}
preservation : ∀ {e e' τ} → [] ⊢ e ∶ τ → e ⟶ e' → [] ⊢ e' ∶ τ
preservation (T-Var x) ()
preservation (T-Field tp fls bnd) (RC-Field ev) =
  T-Field (preservation tp ev) fls bnd
preservation (T-Field (T-New fs₁ tps) fs₂ bnd) (R-Field fs₃ zp bnde)
  rewrite ≡-fields fs₁ fs₂ | ≡-fields fs₂ fs₃ = ⊢-interl zp tps bnd bnde
preservation (T-Invk tp tmt tpl) (RC-InvkRecv ev) =
  T-Invk (preservation tp ev) tmt tpl
preservation (T-Invk tp tmt tpl) (RC-InvkArg evl) =
  T-Invk tp tmt (preservation-list tpl evl)
preservation (T-Invk (T-New fls cp) tmt tpl) (R-Invk rmt zp)
  rewrite ≡-method rmt tmt = subst (⊢-method tmt) tpl zp
preservation (T-New fls tpl) (RC-NewArg evl) =
  T-New fls (preservation-list tpl evl)
\end{spec}

The case for constructor |T-Var| is impossible, because a variable term cannot take a step, and we finish this case using the Agda's absurd |()| pattern. Constructor |T-Field| has two cases: (1) the congruence rule, applying the induction hypothesis in the first expression; (2) the reduction step, where using the auxiliary lemmas |eqFields| and |⊢-zip| we show that the expression |e'| preserves the initial type of expression |e|. The |T-Invk| constructor is the most intricate, with three cases: (1) the congruence rule for the first expression, where we apply the induction hypothesis; (2) the congruence for the list of arguments, where we use an auxiliary proof |preservation-list| which call the induction hypothesis for each argument; (3) the reduction step, where we show that after a reduction step the type is preserved by using the auxiliary lemmas |≡-method|, |⊢-method|, and |subst|\footnote{These lemmas are omitted from this text, but can be found in our source code repository~\cite{repos}.}. This proof is similar to $\lambda$-calculus, using the lemma stating that \emph{Expression substitution preserves typing}~\cite{Igarashi:2001:FJM:503502.503505}. Lastly, |T-New| has only the congruence case for which we apply the induction hypothesis for each argument of the class constructor.

The proof of |progress| for FJ follows the same script as usual: induction on the derivation of the typing rule.

\begin{spec}
progress : ∀ {e τ} → [] ⊢ e ∶ τ → Progress e
progress (T-Var ())
progress (T-Field tp fls bnd) with progress tp
progress (T-Field tp fls bnd) | Step ev = Step (RC-Field ev)
progress (T-Field (T-New flds fts) fls bnd) | Done ev
  rewrite ≡-fields flds fls = Step (R-Field fls (proj₂ (⊧-interl fts))
    (proj₂ (∋-interl fts (proj₂ (⊧-interl fts)) bnd)))
progress (T-Invk tp mt tpl) with progress tp
progress (T-Invk tp mt tpl) | Step ev = Step (RC-InvkRecv ev)
progress (T-Invk tp mt tpl) | Done ev with progress-list tpl
progress (T-Invk tp mt tpl) | Done ev | Step evl =
  Step (RC-InvkArg evl) 
progress (T-Invk (T-New flds fts) mt tpl) | Done ev | Done evl =
  Step (R-Invk mt (proj₂ (⊧-interl tpl)))
progress (T-New fls tpl) with progress-list tpl
progress (T-New fls tpl) | Step evl = Step (RC-NewArg evl)
progress (T-New fls tpl) | Done evl = Done (V-New evl)
\end{spec}

Most cases are simple, as for $\lambda$-calculus. We use the same approach as before: a datatype definition called |Progress| to hold the cases for when the expression is a value or it can take a step. The complicated cases are those for |T-Field| and |T-Invk|, when processing the actual reduction step. When proving \emph{progress} for |T-Field|, to be able to produce a |R-Field| we needed to write two extra lemmas |⊧-interl| and |∋-interl|, which were omitted here for brevity. The case for |T-Invk| also used the lemma |⊧-interl| to produce a |R-Invk|. 

\subsection{Intrinsic Formalization}

In this subsection we present an intrinsically-typed formalization and a definitional interpreter for the same subset of FJ presented in the previous subsection. Here, we show how \emph{de Bruijn} indices can be used to deal with the subtleties of more elaborated binding mechanisms. This calculus uses a nominal type system, which differs from the structural type system of STLC. In our approach, we chose to drop all names, using \emph{de Bruijn} indices to represent \emph{name bindings} for classes, attributes, methods, and variables. First we define a type |Ty| where each class is represented by an index |Fin n| on the class table. Variable |n| represents the amount of classes in the source program, and it is bound as a module parameter in our Agda implementation. 

As we saw earlier, the syntax of FJ presents a mutual relation between expressions and class tables, i.e., a class can contain expressions, and an expression can relate to information in the class table. It gives rise to a cyclic dependency between the two elements, which makes the encoding of an intrinsically-typed syntax for FJ tricky. As a solution, we split the definition of a class in two parts: the \emph{signature} of a class defines only the types of the fields and methods, whereas the \emph{implementation} contains the actual code (expression) to be executed. This definition allows us to type-check expressions using information in the class table.

%format CSig = "\D{CSig}"
%format MSig = "\D{MSig}"
%format CImpl = "\D{CImpl}"
%format MImpl = "\D{MImpl}"
%format CTImpl = "\D{CTImpl}"
%format supers = "\RF{supers}"
%format flds = "\RF{flds}"
%format signs = "\RF{signs}"
%format impls = "\RF{impls}"
%format body = "\RF{body}"

\paragraph{Intrinsically-typed syntax}{We define a class signature |CSig| as a |record| with two fields. The |flds| definition represents the types for each attribute in a class. The |signs| field represents the method signatures, which is defined as a list of |MSig|. It is worth to note that we omit names for attributes and methods, since we are representing them as \emph{de Bruijn} indices.}

\begin{spec}
record CSig : Set where
  field
    flds   : List Ty
    signs  : List MSig
\end{spec}

The method signature is also defined as a |record| with two fields. The first |ret| represents the method return type, and the second |params| a list of types for each method parameter.

\begin{spec}
record MSig : Set where
  field
    ret     : Ty
    params  : List Ty
\end{spec}

%format CTSig = "\D{CTSig}"

We represent the table of \emph{class signatures} as a vector |Vec| (coming from the standard library) and indexed by |n|, representing the number of defined classes in the programmer source-code.

\begin{spec}
CTSig : Set
CTSig = Vec CSig n
\end{spec}

Similarly, we define |CImpl|, |MImpl|, and |CTImpl|\footnote{The details of implementation were omitted from this text, but can be found in our source code repository~\cite{repos}.} to represent the implementation of classes, methods, and class tables, respectively. Using this approach, each instance of |CImpl| is associated with its respective index of a |CSig|, and the field |impls| associates a |body| expression for each method.

%format ξvar = "\V{\xi}"
%format concatMap = "\D{concatMap}"
%format CSig.flds = "\RF{CSig.flds}"
%format CSig.supers = "\RF{CSig.supers}"

\paragraph{Auxiliary functions}{As for the extrinsically defined version of FJ, we have auxiliary definitions to obtain information from the class table. Function |fields| provides a list of all available attributes of a given class. The class table |Δ| is bound as a module parameter.}

\begin{spec}
fields : Ty → List Ty
fields τ = CSig.flds (lookup Δ τ)
\end{spec}

%format signatures = "\D{signatures}"
%format CSig.signs = "\RF{CSig.signs}"

Similarly to fields, the function |signatures| provides a list of all available method signatures of a given class.

\begin{spec}
signatures : Ty → List MSig
signatures τ = CSig.signs (lookup Δ τ)
\end{spec}

%format implementations = "\D{implementations}"
%format lookup-allFin = "\D{lookup\textrm{-}allFin}"
%format sym = "\D{sym}"
%format CImpl.impls = "\RF{CImpl.impls}"
%format δ = "\V{\delta}"

We also have a function to retrieve the |implementations| of a given class, which returns a list of all method implementations. We use the functions |sym| and |lookup-allFin| from Agda's standard library to associate the signatures with its implementations.

\begin{spec}
implementations : (τ : Ty) → CTImpl → All MImpl (signatures τ)
implementations τ δ rewrite sym (lookup-allFin τ) =
  CImpl.impls (lookup τ δ)
\end{spec}

%format Maybe = "\D{Maybe}"
%format Δ = "\V{\Delta}"
%format ξ = "\RF{\xi}"
%format MSig.params = "\RF{MSig.params}"
%format MSig.ret = "\RF{MSig.ret}"

Once we have the definition of a class table, we can define the inherently-typed syntax for expressions. We start by defining an object-level type context |Ctx| encoded as a list of types (similar to STLC), which is used to store variable types. We represent each judgment of the FJ's static semantics as a constructor. As we mentioned before, FJ expressions can refer to information from two different sources: (1) on a well-formed class table |Δ|, which is defined globally after importing the class table module; (2) on variables in the type context |Γ|, which is expected as a parameter for the inductive datatype definition. Similarly to the intrinsically-typed definition of STLC, the |Expr| datatype is \emph{indexed} by |Ty|, which represents the expected result type for the expression. The representation of expressions is defined in the code as follows. The reader can note that, to express the intrinsically-typed syntax, we use only \emph{signatures}, never \emph{implementations}.

\begin{spec}
data Expr (Γ : Ctx) : Ty → Set where
  Var    : ∀ {x}   → x ∈ Γ → Expr Γ x
  Field  : ∀ {c f} → Expr Γ c → f ∈ (fields c) → Expr Γ f
  Invk   : ∀ {c m} → Expr Γ c → m ∈ (signatures c)
        → All (Expr Γ) (MSig.params m) → Expr Γ (MSig.ret m)
  New    : ∀ c → All (Expr Γ) (fields c) → Expr Γ c
\end{spec}

The constructor for |Var| is encoded the same way as for STLC, where we use a well-typed \emph{de Bruijn} index |x ∈ Γ| which binds the type for variable |x|. The result type of this expression should be the one represented by the |x| variable.

The constructor |Field| expects an expression of type |c| and a \emph{de Bruijn} index |f ∈ (fields c)|. Again, we represent the expected field using a similar scheme to the one used for variables. Here |f| is the type of the expected field, |c| is the index of the given class, and |fields c| returns a list containing all the fields of the class represented by |c|. The result type |Expr Γ f| states that the expression has the type defined in |f|.

The constructor |Invk| receives three parameters, where the first is an expression having type |c|, the second a \emph{de Bruijn} index |m ∈ (signatures c)|, and the third uses the predicate |All| to associate each parameter with its expected type (|MSig.params m|). The result type for this expression |Expr Γ (MSig.ret m)| should be the one coming from the method's return type |MSig.ret m|. The constructor for |New| receives first an index representing a class |c|, and then similarly to the |Invk| constructor, it uses the predicate |All| to enforce each parameter to have the expected type using the information coming from a call of function |fields c|. The result type of this constructor is the type of the class |c|, which is being instantiated.

%format VNew = "\Con{VNew}"
%format <: = "\D{<:}"

\paragraph{Values and environments}{This procedure is the same adopted when defining the intrinsic version of STLC. First we define a |Val|, which in FJ has only one constructor representing an object creation with all parameters also being a value. Here we also use the predicate |All| to guarantee this restriction.}

\begin{spec}
data Val : Ty → Set where
  V-New : ∀ c → All Val (fields c) → Val c
\end{spec}

And then, we define an |Env|, which links each type on the context |Γ| with a value |Val|.

\begin{spec}
Env : Ctx → Set
Env Γ = All Val Γ
\end{spec}

%format CTImpl = "\D{CTImpl}"
%format just = "\Con{just}"
%format nothing = "\Con{nothing}"
%format suc = "\Con{suc}"
%format γ = "\V{\gamma}"
%format ∈-lift = "\D{\in\hspace{-3pt}\textrm{-}lift}"
%format eval-list = "\D{eval\textrm{-}list}"
%format let = "\K{let}"
%format in = "\K{in}"
%format Fuel = "\D{Fuel}"
%format MImpl.body = "\RF{MImpl.body}"

\paragraph{Definitional Interpreter}{Having all the building blocks to make the FJ interpreter, we can define the |eval| function. It receives four arguments, and returns a |Maybe| value. The first argument is the fuel, encoded as a natural number (|Fuel = ℕ|), used to ensure that the evaluator always terminates~\cite{Amin:2017:TSP:3093333.3009866,Owens:2016:FBS:3089528.3089551}. The second parameter is the \emph{implementation} of a class table. The third parameter is the run-time variable environment. And the last one is the expression |Expr| to be evaluated. The return of this function will provide a |Val c| in case of success, or |nothing| when the fuel runs out.}

\begin{spec}
eval : Fuel → CTImpl → Env Γ → Expr Γ c → Maybe (Val c)
eval zero δ γ e = nothing
eval (suc f) δ γ (Var x) = just (lookup γ x)
eval (suc f) δ γ (Field e x) with eval f δ γ e
... | nothing = nothing
... | just (V-New c cp) = just (lookup cp x)
eval (suc f) δ γ (Invk e m mp) with eval f δ γ e
... | nothing = nothing
... | just (V-New c cp) with eval-list f δ γ mp
...   | nothing = nothing
...   | just mp' = let mi = lookup (implementations c δ) m
                     in eval f δ mp' (MImpl.body mi)
eval (suc f) δ γ (New c cp) with eval-list f δ γ cp
... | nothing = nothing
... | just cp' = just (V-New c cp')
\end{spec}

As we are using \emph{fuel based evaluation}~\cite{Amin:2017:TSP:3093333.3009866,Owens:2016:FBS:3089528.3089551}, we pattern match first on the |fuel| argument. It has two cases: |zero| when the fuel counter reaches zero, and our evaluation function returns |nothing|, or |suc fuel| when there is still fuel to proceed with the evaluation. Then we pattern match with the expression being evaluated, with one case for each FJ syntactic constructor. The case for |Var| is the same of STLC, except here the result is embedded in a Maybe monad. For |Field| first we have to evaluate the expression |e|, and then it is necessary to |lookup| the \emph{de Bruijn} index |f| on the argument list |cp|. For the |Invk| constructor, we have to evaluate the expression |e| and the list of arguments |mp|, and then, using the |implementations| function, we select the method |m|, to evaluate its body, using the evaluated method parameters |mp'| as the |γ| environment. Lastly, to evaluate |New|, we have to evaluate the parameters |cp|. For all recursive cases, we decrement the |fuel| parameter to guarantee termination, since FJ can implement recursion, and thus run indefinitely. It is worth noticing that the only way the |eval| function can result in |nothing| is when the fuel reaches zero. Again, we highlight here that there is no need for error control regarding to indices, since we have ensured everything is well-scoped using \emph{de Bruijn} indices.

\subsection{Elaborating FJ Extrinsic to Intrinsic}

%format elabCtx = "\D{elabCtx}"
%format elabExpr = "\D{elabExpr}"
%format elabExprs = "\D{elabExprs}"
%format elabVar = "\D{elabVar}"
%format elabField = "\D{elabField}"
%format elabMeth = "\D{elabMeth}"
%format eq-fields = "\D{eq\textrm{-}fields}"
%format eq-mparams = "\D{eq\textrm{-}mparams}"
%format Name⇒Ty = "\D{Name{\Rightarrow}Ty}"
%format flds = "\V{flds}"

Similarly to STLC, we also elaborate the extrinsic syntax of FJ to the intrinsic version using the |elabExpr| function. Since in the intrinsic formalization of FJ we use \emph{de Bruijn} indices instead of names (to represent variables, attributes, methods, and classes), we had to define one function to elaborate each name to its correspondent intrinsic index. Thus, the function |elabVar| is used to elaborate a variable name to an index, |elabField| and |elabMeth| work the same way for fields and methods. We also encoded the |elabExprs| function to recursively apply |elabExpr| for each parameter when elaborating the method and constructor parameters, and function |Name⇒Ty| to produce an index for a given class name.

\begin{spec}
elabExpr : ∀ {Γ e τ} → Γ ⊢ e ∶ τ → Expr (elabCtx Γ) (Name⇒Ty τ)
elabExpr (T-Var x) = Var (elabVar x)
elabExpr (T-Field wte fls wtf) = Field (elabExpr wte) (elabField fls wtf)
elabExpr (T-Invk {Γ = Γ} wte wtm wtmp) =
  Invk (elabExpr wte) (elabMeth wtm)
     (subst (All (Expr (elabCtx Γ))) (eq-mparams wtm) (elabExprs wtmp))
elabExpr (T-New {Γ = Γ} {C = C} flds wtcp) =
  New (Name⇒Ty C)
      (subst (All (Expr (elabCtx Γ))) (eq-fields flds) (elabExprs wtcp))
\end{spec}

\section{Comparing the Extrinsic and Intrinsic Formalizations}
\label{sec:compare}

We have described in this paper the formalization of two programming languages in Agda using the syntactical (extrinsic) and functional (intrinsic) approaches. We presented the process of writing the relational semantics rules together with soundness proofs and the intrinsically-typed syntax together with a definitional interpreter to achieve a similar result. In this section we compare the resulting specifications using two metrics: lines of code, and number of high-level structures.

Table \ref{tab:loc} compares our two language definitions considering the \emph{extrinsic} and \emph{intrinsic} formalization approaches regarding to the approximate number of lines-of-code\footnote{We call here ``approximate'' because we are not considering lines to create/import modules, and some break lines to improve readability.} (LOC) to provide a type soundness result. Roughly, the table shows us that, if we consider the sum of all modules (\emph{Total}), we have to write a considerable amount of lines when applying the extrinsic compared to its intrinsic version. However, to express the syntax and evaluation rules, we used similar amount of lines of code. The main difference between both approaches is that we do not need to write any line to define the type-checker nor the soundness proofs using the intrinsic approach (since it guarantees safety-by-construction). 

\begin{table}[!htb]
\begin{center}
\begin{tabular}{lcccc}    
\hline
             & Ext. STLC & Int. STLC & Ext. FJ & Int. FJ \\ \hline
Syntax       & 10           & 10           & 19           & 26           \\
Typing Rules & 16           & 0            & 39           & 0            \\
Evaluation   & 22           & 8            & 40           & 25           \\
Proofs       & 75           & 0            & 99           & 0            \\ 
Auxiliary & 8           & 12           & 23           & 13           \\ \hline 
\emph{Total} & 131          & 30           & 220          & 64           \\ \hline
\end{tabular}
\caption{Approximate sizes (in LOC) for our STLC and FJ developments.}
\label{tab:loc}
\end{center}
\end{table}

Obviously, lines of code is only one metric which can be used to compare the expressivity of each approach, and not its complexity. The main advantage of using an extrinsic approach is to have a depth control over the structures and the semantics, being able to follow step-by-step during the proof construction. Also, by using proof assistants with proof automation mechanisms (such as Coq), we could decrease considerably the number of lines to prove the same theorems. For the intrinsic version, an advantage is that type safety becomes a guiding contract when writing a program, and this guarantee comes from the host language used in the development. Furthermore, we can reuse more code from Agda's standard library.

In Table \ref{tab:nrfun} we present a comparison of the number of high-level structures developed in our source-code formalizations. Again, we can see that using the intrinsic version, we can express the syntax, typing rules, evaluation and proofs using a small number of high level definitions (functions or lemmas, and inductive definitions). We can see that for the case of STLC, it naturally fits into Agda's definition, since both languages are functional. For the case of FJ, the intricate relation between its imperative features forces us to express its internal features using some extra high-level structures than for STLC. However, we could express both languages using less high-level structures in the intrinsic version when compared with its respective extrinsic one.

\begin{table}[!htb]
\begin{center}
\begin{tabular}{lcccc}
\hline
                          & Ext. STLC & Int. STLC & Ext. FJ & Int. FJ \\ \hline
Nr. Functions/Lemmas      & 10        & 2         & 21      & 5       \\
Nr. Inductive Definitions & 9         & 3         & 19      & 10      \\ \hline
\end{tabular}
\caption{Number of functions and inductive definitions for our STLC and FJ developments.}
\label{tab:nrfun}
\end{center}
\end{table}

Although there is a considerable difference between the LOC and high-level structures considering the different approaches to formalize a programming language in Agda, we could note during our development that the intrinsic version requires creativity and insight to find the correct representation of the semantics, which is relatively simple for the extrinsic one. Usually, in the extrinsic approach we have to basically translate the relation on the structural operational semantics of the language into the proof assistant, and follow the script to prove type soundness. The most difficult part is to reason on how to break the proofs in small lemmas, so they are accepted by the proof assistant. For the intrinsic case, sometimes we have to tweak some definitions, to model the necessary invariants to obtain a type soundness result. This effort could be noted in our intrinsic formalization of FJ, where we had to split the definition of a class table in signatures and implementations to allow the intrinsically-typed syntax to be sound-by-construction.

\section{Related Work}
\label{sec:related}

There is a vast body of literature on soundness and proof techniques regarding programming languages. The most relevant styles are from Wright and Felleisen's syntactic approach~\cite{Wright:1994:SAT:191905.191909}, Plotkin's structural operational semantics~\cite{Plotkin2004ASA}, Kahn's natural semantics~\cite{Kahn:1987:NS:28220.28222}, and Reynold's definitional interpreters~\cite{Reynolds:1972:DIH:800194.805852}. Although the common ground is to find mechanized formalization using more syntactic (extrinsic) approaches, we could see the number of functional (intrinsic) encodings of semantics increasing in recent years.

Considering the extrinsic approach, there are several papers describing the mechanization of both, $\lambda$-calculus and Featherweight Java. For example, in their book, Pierce et al.~\cite{pierce2019software} describe the formalization of STLC in Coq, and Wadler~\cite{Wadler-plfa} present the formalization of STLC in Agda. We applied a simplified version of the ideas presented in these books in our formalization of STLC. Besides these books, there are several other papers mechanizing different versions of $\lambda$-calculus~\cite{Ribeiro2013,Donnelly:2007:FSN:1247762.1248307}. Regarding Featherweight Java, there are some projects describing its formalization. Mackay et al.~\cite{Mackay:2012:EFJ:2318202.2318206} developed a mechanized formalization of FJ with assignment and immutability in Coq, proving type-soundness for their results. Delaware et al.~\cite{Delaware:2011:PLT:2076021.2048113} used FJ as basis to describe how to engineer product lines with theorems and proofs built from feature modules, also carrying the formalization Coq. Both papers inspired us in our modeling of FJ. As far as we know, our work is the first to formalize FJ in Agda using the extrinsic approach.

The formalization of programming languages combining an inherently-typed syntax (showed in \cite{Altenkirch:1999:MPL:647849.737066, Augustsson99anexercise, Reynolds01whatdo}) and definitional interpreters has also been made more often. Danielsson~\cite{Danielsson:2012:OSU:2364527.2364546} used the co-inductive partiality monad to formalize $\lambda$-calculus using total definitional interpreters, demonstrating that the resulting semantics are useful type-soundness results. Benton et al.~\cite{Benton2012} used Coq to formalize an intrinsic version of STLC using \emph{de Bruijn} indices to deal with name binding. In his book, Wadler~\cite{Wadler-plfa} also discuss the definition of STLC using an intrinsically-typed approach. We can find some other results applying these techniques~\cite{McBride:2010:OBM:1863495.1863497, Altenkirch:2016:TTT:2914770.2837638}. On the formalization of modern programming languages (such as Java), Affeldt and Sakaguchi~\cite{JFR4317} present an intrinsic encoding in Coq of a subset of C applying it to TLS network processing, Owens et al.~\cite{Owens:2016:FBS:3089528.3089551} advocate for the use of a definitional interpreter written in a purely functional style in a total language. Amin and Rompf~\cite{Amin:2017:TSP:3093333.3009866} show how type soundness proofs for advanced, polymorphic, and object-oriented type systems can be carried out with an operational semantics based on definitional interpreters implemented in Coq. More closely to our intrinsic formalization of FJ, Bach Poulsen et al.~\cite{BachPoulsen:2017:IDI:3177123.3158104} present a formalization of Middleweight Java (a variant of FJ) defined in Agda and some techniques to deal with name binding. In our formalization, we used only standard techniques (like \emph{de Bruijn} indices) to formalize FJ, trying to keep the code as simple as possible to facilitate readability and maintainability.

\section{Conclusion}
\label{sec:conclusion}

In this paper, we discussed the formalization of two well-known programming languages using the syntactic (extrinsic) and functional (intrinsic) approaches in the Agda programming language. For the first language, the simply typed lambda calculus, we were able to analyze the differences between each approach to prove type-soundness in a small and controlled setting. In the subsequent section, we shown the formalization of a large subset of Featherweight Java, dealing with its mutual related structure and complex binding mechanisms. For both languages and scenarios we could observe the complexities of each approach, and their advantages. By using an extrinsic formalization, we can have access to all the steps when processing the static and dynamic semantics, while using the intrinsic version we avoid repetitions and receive type soundness proofs (almost) for free. We believe that this paper can also be useful to be a starting point on the formalization of more complex programming languages in Agda.

Several branches can be explored as future work. For example, we still need to integrate the research in this paper with a parser that can be applied to both extrinsic and intrinsic syntax that our interpreters take as input. We also intend to extend the formalization of STLC and FJ with more features, like mutable state, sub-typing, polymorphism, dynamic dispatch, etc., studying which features do enjoy the safety properties. Another path we intend to follow is the formalization of a equivalence proof for both formalization approaches.

%% The Appendices part is started with the command \appendix;
%% appendix sections are then done as normal sections
%% \appendix

%% \section{}
%% \label{}

%% If you have bibdatabase file and want bibtex to generate the
%% bibitems, please use
%%
%%  \bibliographystyle{elsarticle-num} 
%%  \bibliography{<your bibdatabase>}

\section*{Acknowledgment}

This material is based upon work supported by CAPES/Brazil - Finance Code 001.

\pagebreak

\section*{References}

\bibliographystyle{elsarticle-num} 
\bibliography{references}

\end{document}
\endinput
%%
%% End of file `elsarticle-template-num.tex'.
