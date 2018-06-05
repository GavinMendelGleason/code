\documentclass{llncs}


%%%%%%%%%%%%%%%%% Preamble %%%%%%%%%%%%%%%%%%%%%%%

%% Fix Margins 
%\usepackage[margin=1in]{geometry}

\usepackage{listings}
\usepackage{amsfonts}
\usepackage{xcolor}
\usepackage{graphicx}

% Equations
\usepackage{amsmath}

% Fonts
\usepackage{amssymb}
\usepackage{bbm}
\usepackage[greek,english]{babel}
\usepackage{textgreek}
\usepackage{stmaryrd}

%handles sizes
\usepackage{anyfontsize}

%% This handles the translation of unicode to latex:
%\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{autofe}

%% Some convenient shorthands
\newcommand{\AD}{\AgdaDatatype}
\newcommand{\AF}{\AgdaFunction}
\newcommand{\AB}{\AgdaBound}
\newcommand{\AIC}{\AgdaInductiveConstructor}
\newcommand{\AM}{\AgdaModule}
\newcommand{\AP}{\AgdaPrimitive}
\newcommand{\AS}{\AgdaString}
\newcommand{\AR}{\AgdaRecord}
\newcommand{\AK}{\AgdaKeyword}
\newcommand{\AO}{\AgdaOperator}
% Better use this one!

\usepackage{agda}
%include agda.fmt

\usepackage{bussproofs}

%% Lambda Calculus (should be a .sty at some point) 
\definecolor{typeColour}              {HTML}{0000CD}
\definecolor{judgementColour}         {HTML}{008B00}

\newcommand{\atype}[1]{\textcolor{typeColour}{#1}}

\newcommand{\ofty}[2]{{#1}{:}{#2}}
%\newcommand{\ofty}[2]{{#1}\colon\kern-.15em{#2}}
\newcommand{\bigofty}[2]{{#1} \textcolor{judgementColour}{\;:\;} { \atype{#2} }}
\newcommand{\lam}[3]{\lambda(\ofty{#1}{ \atype{#2} }).{#3}}
\newcommand{\app}[2]{{#1}\circ{#2}}
\newcommand{\bred}{\;\Rightarrow_{\beta}\;}
\newcommand{\subst}[2]{ [{#1} := {#2}] }

\newcommand{\seq}[3]{{#1} \textcolor{judgementColour}{\;\vdash\;} \bigofty{#2}{#3} }

\newcommand{\oseq}[2]{{#1} \textcolor{judgementColour}{\;\vdash\;} {#2}}

\newcommand{\imp}[2]{{#1} \rightarrow {#2}}

\newcommand{\impElim}{$E^{\rightarrow}$}


%% Some characters that are not automatically defined
%% (you figure out by the latex compilation errors you get),
%% and you need to define:
%
%\DeclareUnicodeCharacter{8988}{\ensuremath{\ulcorner}}
%\DeclareUnicodeCharacter{8989}{\ensuremath{\urcorner}}
%\DeclareUnicodeCharacter{8803}{\ensuremath{\overline{\equiv}}}
\DeclareUnicodeCharacter{8799}{\ensuremath{\stackrel{{!!}}{=}}}
\DeclareUnicodeCharacter{8759}{\ensuremath{\colon\colon}}
\DeclareUnicodeCharacter{7477}{\ensuremath{^{I}}}
\DeclareUnicodeCharacter{7472}{\ensuremath{^{D}}}
\DeclareUnicodeCharacter{7580}{\ensuremath{^{C}}}
\DeclareUnicodeCharacter{7488}{\ensuremath{^{T}}}
\DeclareUnicodeCharacter{7480}{\ensuremath{^{L}}}
\DeclareUnicodeCharacter{7486}{\ensuremath{^{P}}}
\DeclareUnicodeCharacter{7484}{\ensuremath{^{O}}}
\DeclareUnicodeCharacter{7584}{\ensuremath{^{F}}}
\DeclareUnicodeCharacter{7468}{\ensuremath{^{A}}}
\DeclareUnicodeCharacter{2208}{\ensuremath{\in}}
\DeclareUnicodeCharacter{956}{\ensuremath{\mu}}
%% Add more as you need them (shouldn’t happen often). 

%% Hyper ref for \url support
\usepackage{hyperref}

%%%%%%%%%%%%%%%%%%% Paper %%%%%%%%%%%%%%%%%%%%%%%%%%
\title{Model Checking the Semantic Web with the Modal μ-Calculus}
\author{Gavin Mendel-Gleason\\ 
Trinity College Dublin}

\begin{document}

\maketitle 

%% 1. Who are the intended readers(3-5 names)
%% 2. What did you do?(50 words)
%% 3. Why did you do that?(50 words) - why did it need to be done in the field?
%% 4. What happened when you did it? (50 words)
%% 5. What do the results mean in theory(50 words)
%% 6. What  do the results mean in practice(50 words)
%% 7. (NB most impt q) What is the key benefit for readers?(25 words)
%% 8. What remains unresolved (no word limit)

\begin{abstract} The Linked Data community has made use of storage
formats which are abstractly representations of labelled
multidigraphs. In order to constrain or check the properties of these graphs
various techniques have been used including approaches such as OWL,
based on description logics, and SHACL which is a more constraint
based approach.

Practitioners have found that for certain data storage and
data-quality needs, the constraint based approach is more
natural. Since finite graphs can be viewed as a labelled transition
system we can make use of the well studied Modal μ-calculus to provide
succinct descriptions of graph properties with a constraint based
approach. We demonstrate an implementation of an interpreter for the
Modal μ-calculus in the Agda proof-assistant which functions over RDF
triples and literals. The language can be used either as a query
language, showing all subject URIs which satisfy some formula, or as a
checker which determines whether some URI satisfies a
formula.\end{abstract}

\section{Introduction}

Triple stores present a database-like storage solution for Linked
Data. When we have already accumulated some fragment of the web of
data, it can be useful to reason about this data such that we can
check for consistency or data quality. Such applications however are
not well suited to open-world interpretations of data using ontology
modelling languages such as OWL.  Instead, in these cases, reasoning
is more naturally done using constraint based approaches which take a
closed-world view of data. Practitioners in the field have developed
SHACL as an answer to the need for such a language.

The Modal μ-calculus can describe properties of labelled transition
systems with a concise and expressive language. Since labelled
transition systems are formally equivalent to labelled graphs, these
approaches can be repurposed for the specification of properties and
constraints for graphs.


We
show that SHACL .

However, practioners have
recognised the need for constraint languages for triple stores. For
certain industry and applications


Once data is being evaluated
and queried it is no longer as useful to take an {\em open world }
view on data.

For instance, cardinality has a very weak meaning when interpreted as
open world.


For this reason, languages such as SHACL have been developed in order
to ensure that 


\section{Acknowledgement}

This research is partially supported by the European Union European Union's
Horizon 2020 research and innovation programme under grant agreement No
644055 (ALIGNED, \url{www.aligned-project.eu}).

\bibliographystyle{plain}
\bibliography{export.bib}

\end{document}

