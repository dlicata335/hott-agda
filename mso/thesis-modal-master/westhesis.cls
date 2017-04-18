%%
%% This is file `westhesis.cls',
%% generated with the docstrip utility.
%%
%% The original source files were:
%%
%% westhesis.dtx  (with options: `class')
%%   westhesis Document Class (N. Danner)

%% westhesis:  Document class for Wesleyan University theses.
%% N. Danner (ndanner@wesleyan.edu)
%% Copyright 1999--2011

%% The following RCS info is from the iuthesis class upon which westhesis
%% is based.
%%
%% RCS Info:
%%      iuthesis.dtx,v 1.2.0.23 1999/06/04 14:30:00 ndanger Exp


\def\fileversion{1.0}
\def\filedate{March 2011}








\iffalse





%%\item[ma] For a Master of Arts dissertation.

%%\item[ms] For a Master of Science dissertation.

%%\item[three] Use this if you only have three people on your committee
%%(including your advisor).
\fi



























\iffalse
\fi
\iffalse
\fi

\iffalse
\fi





\iffalse
\fi



\iffalse
\fi





\iffalse
\fi







\NeedsTeXFormat{LaTeX2e}[1996/12/01] \ProvidesClass{westhesis}
\message{<< Class 'westhesis', v\fileversion, \filedate (N. Danner) >>}

\newif\ifWT@debugging \WT@debuggingtrue \WT@debuggingfalse
\def\WT@dbgmsg#1{\ifWT@debugging\message{#1}\fi}
\def\WT@optionmsg#1{\message{  westhesis option: #1}}

\def\WTdraftmsg#1{}
\let\draftmsg\WTdraftmsg
\def\WT@showdraftfoot{}
\DeclareOption{draft}{
  \WT@optionmsg{draft}
  \def\WTdraftmsg#1{\gdef\WT@showdraftfoot{#1}}
  \let\draftmsg\WTdraftmsg
  \def\WT@showdraftfoot{DRAFT: \today}
  \PassOptionsToClass{draft}{amsbook}
}

\DeclareOption{final}{
  \WT@optionmsg{final}
  \def\WTdraftmsg#1{}
  \let\draftmsg\WTdraftmsg
  \def\WT@showdraftfoot{}
  \PassOptionsToClass{final}{amsbook}
}

\newcount\WT@abstype
\newcount\WT@nmlabstract\WT@nmlabstract=0
\newcount\WT@umiabstract\WT@umiabstract=1
\newcount\WT@ugsabstract\WT@ugsabstract=2
\WT@abstype=\WT@nmlabstract
\DeclareOption{umiabstract}{
  \WT@optionmsg{umiabstract}
  \WT@abstype=\WT@umiabstract
  \AtEndOfClass{\raggedbottom}
}
\newif\ifWT@ugsabs
\WT@ugsabsfalse
\DeclareOption{ugsabstract}{
  \WT@optionmsg{ugsabstract}
  \WT@abstype=\WT@ugsabstract
  \AtEndOfClass{\raggedbottom}
}

\newif\ifWT@abstractsigs
\DeclareOption{abstractsigs}{
  \WT@optionmsg{abstractsigs}
  \WT@abstractsigstrue
}
\DeclareOption{noabstractsigs}{
  \WT@optionmsg{noabstractsigs}
  \WT@abstractsigsfalse
}

\newif\ifWT@noabstract
\WT@noabstractfalse
\DeclareOption{noabstract}{
  \WT@optionmsg{noabstract}
  \WT@noabstracttrue
}


\newif\ifWT@three
\DeclareOption{three}{\WT@threetrue}

\DeclareOption{single}{
  \AtEndOfClass{\def\WT@blstretch{1}}
}

\DeclareOption{debug}{
  \WT@debuggingtrue
}

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{amsbook}}
\ExecuteOptions{noabstractsigs,draft}
\ProcessOptions

\PassOptionsToClass{oneside}{amsbook}
\LoadClass{amsbook}[1995/01/27]

\topmargin 0pt
\oddsidemargin=.5in
\evensidemargin=\oddsidemargin
\advance\headheight 2pt
\textwidth 5.75in
\textheight 8.9in
\advance\textheight by -\headheight
\advance\textheight by -\headsep
\advance\textheight by -\footskip
\marginparwidth 0.5in


\def\ps@chapter{
  \gdef\ps@headings{
    \def\@oddhead{
      \normalfont\scriptsize\hfil\rightmark{}{}\hfil \llap{\thepage}
    }
    \def\@oddfoot{
      \normalfont\ttfamily\scriptsize\rlap{\WT@showdraftfoot\hfill}\hfill
    }
    \global\let\@evenfoot\@oddfoot
    \global\let\@mkboth\markboth
    \global\let\partmark\@gobble
    \gdef\chaptermark{%
      \@secmark\markboth\chapterrunhead{}}%
    \global\let\sectionmark\@gobble
  }
}

\def\ps@section{
  \gdef\ps@headings{
    \def\@oddhead{
      \normalfont\scriptsize\hfil\rightmark{}{}\hfil \llap{\thepage}
    }
    \def\@oddfoot{
      \normalfont\ttfamily\scriptsize\rlap{\WT@showdraftfoot\hfill}\hfill
    }
    \global\let\@evenfoot\@oddfoot
    \global\let\@mkboth\markboth
    \global\let\partmark\@gobble
    \gdef\chaptermark{%
      \@secmark\markboth\chapterrunhead{}}%
    \gdef\sectionmark{%
      \@secmark\markboth\sectionrunhead{}}%
  }
}

\def\ps@chapsec{
  \gdef\ps@headings{
    \def\@oddhead{
      \normalfont\scriptsize\rlap{\leftmark{}{}}\hfill\llap{\rightmark{}{}}
    }
    \def\@oddfoot{
      \normalfont\scriptsize\rlap{\ttfamily\WT@showdraftfoot\hfill}%
      \hfil\thepage\hfil
    }
    \global\let\@evenfoot\@oddfoot
    \global\let\@mkboth\markboth
    \global\let\partmark\@gobble
    \gdef\chaptermark{%
      \@secmark\markboth\chapterrunhead\chaptername}%
    \gdef\sectionmark{
      \@secmark\markright\WT@sectionrunhead{}}
  }
}

\def\WT@sectionrunhead#1#2#3{%
  \def\@tempa{#3}%
    \ifx\@empty\@tempa\else%
    \@ifnotempty{#2}{\uppercase{#1 #2}\@ifnotempty{#3}{. }}%
    \ifx\@empty\@tempa\else\uppercasenonmath\@tempa\@tempa\fi%
  \fi%
}

\def\ps@plain{\ps@empty
  \def\@oddfoot{
    \normalfont\scriptsize
    \rlap{\ttfamily\WT@showdraftfoot}\hfil\thepage\hfil
  }
  \let\@evenfoot\@oddfoot
}

\renewcommand{\author}[1]{\gdef\@author{#1}}\let\@author\relax
\renewcommand{\title}[1]{\gdef\@title{#1}}
\let\@title\relax

\def\submitdate#1{\gdef\@submitdate{#1}}\let\@submitdate\relax
\def\department#1{\gdef\@department{#1}}\let\@department\relax
\def\departmentname#1{\gdef\@departmentname{#1}}\departmentname{Department}
\def\degree#1{\gdef\@degree{#1}}\degree{Doctor of Philosophy}

\def\advisor#1{\gdef\@principaladvisor{#1}}\let\@principaladvisor\relax
\def\secondreader#1{\gdef\@secondreader{#1}}\let\@secondreader\relax
\def\thirdreader#1{\gdef\@thirdreader{#1}}\let\@thirdreader\relax
\def\fourthreader#1{\gdef\@fourthreader{#1}}\let\@fourthreader\relax
\def\fifthreader#1{\gdef\@fifthreader{#1}}\let\@fifthreader\relax

\def\copyrightyear#1{\gdef\@copyrightyear{#1}}
\let\@copyrightyear\relax



\newbox\dedicationbox
\newenvironment{dedication}{%
  \global\let\dedication\relax%
  \bgroup
  \renewcommand{\baselinestretch}{1}
  \normalsize
  \global\setbox\dedicationbox\vbox\bgroup%
  \begin{center}
}{
  \end{center}
  \egroup\egroup
}


\newbox\acknowledgebox
\newenvironment{acknowledgements}{%
  \global\let\acknowledgements\relax%
  \bgroup
  \renewcommand{\baselinestretch}{\WT@blstretch}
  \normalsize
  \global\setbox\acknowledgebox\vbox\bgroup
  \trivlist%
    \item[]\ignorespaces
}{
  \endtrivlist
  \egroup\egroup
}

\renewenvironment{abstract}{%
  \global\let\abstract\relax%
  \bgroup%
  \renewcommand{\baselinestretch}{\WT@blstretch}%
  \normalsize%
  \global\setbox\abstractbox\vbox\bgroup
  \trivlist\item[]\ignorespaces
}%
{
  \endtrivlist
  \egroup\egroup
  \global\let\endabstract\relax
}

%% If \option{ugsabstract} or \option{umiabstract}
%% has been specified, then the abstract should be typeset with no page numbers.
%% If \option{umiabstract} or \option{ugsabstract}
%% has been specified, print the advisor's name or the signature lines,
%% respectively.  This could be done with an |\ifcase|, but seems less
%% transparent when re-reading the code.
\def\WT@defineabstract{
  \gdef\makeabstract{
    \typeout{Abstract}
    \bgroup
    \normalfont
    \ifnum\WT@abstype>0%
      \WT@dbgmsg{makeabstract: Setting abstract pagestyle empty}%
      \pagestyle{empty}\thispagestyle{empty}%
    \else%
      \WT@dbgmsg{makeabstract: Setting abstract pagestlye plain}%
    \fi%
    \ifnum\WT@abstype>0%
      \WT@dbgmsg{makeabstract: Setting title}%
      \begin{center}%
      \check@val\@author \\[.5\baselineskip]
      \check@val\@title
      \end{center}%
      \vskip\baselineskip
      \WT@dbgmsg{makeabstract: Done}%
    \else%
      \WT@dbgmsg{makeabstract: Setting title}%
      \@makeschapterhead{Abstract}
    \fi%
    \WT@dbgmsg{makeabstract: Setting abstract}%
    \unvbox\abstractbox
    \ifnum\WT@abstype=\WT@umiabstract%
      \WT@dbgmsg{makeabstract (umi): advisor's name}%
      \vskip\baselineskip%
      \hbox to\hsize{\hfill\check@val\@principaladvisor, Ph.D.}%
    \fi
    \ifnum\WT@abstype=\WT@ugsabstract%
      \WT@dbgmsg{makeabstract (ugs): signature lines}%
      \ifWT@abstractsigs%
      \vbox{
\hbox to\textwidth{%
  \WT@sig[2.5in]{\check@val\@principaladvisor, Ph.D.}\hfill%
  \WT@sig[2.5in]{\check@val\@thirdreader, Ph.D.}%
}%
\hbox to\textwidth{%
  \WT@sig[2.5in]{\check@val\@secondreader, Ph.D.}\hfill%
  \ifWT@three\else\WT@sig[2.5in]{\check@val\@fourthreader, Ph.D.}\fi%
}%
\ifx\@fifthreader\relax\else%
  \hbox to\textwidth{%
    \hfill\WT@sig[2.5in]{\check@val\@fifthreader, Ph.D.}%
  }%
\fi%
      }
      \fi
    \fi
    \newpage
    \egroup
    \ifnum\WT@abstype>0
      \def\end@fterabstract{\end{document}}
    \else
      \def\end@fterabstract{}
    \fi
    \end@fterabstract
  }
}

\ifWT@noabstract
  \ifnum\WT@abstype>0\WT@defineabstract\else\def\makeabstract{}\fi
\else
  \WT@defineabstract
\fi

\ifnum\WT@abstype>1
  \WT@dbgmsg{Setting maketitle noop}
  \def\maketitle{}
\else
  \def\maketitle{
    \bgroup
\thispagestyle{empty}
\hrule\vskip.5ex
\noindent Wesleyan University\hfill The Honors College
\vskip.5ex\hrule
\vskip3in
\bgroup
\Large
\begin{center}\check@val\@title\end{center}
\egroup
\vskip.25in
\bgroup
\large
\begin{center}
by \\[\baselineskip]
\check@val\@author
\end{center}
\egroup
\vfill
\bgroup
\large
\begin{center}
A thesis submitted to the\\
faculty of Wesleyan University\\
in partial fulfillment of the requirements for the\\
Degree of Bachelor of Arts\\
with Departmental Honors in \check@val\@department
\end{center}
\vskip\baselineskip
\hrule
\vskip.5ex
\noindent Middletown, Connecticut\hfill\check@val\@submitdate
\vskip.5ex
\hrule
\egroup
\egroup
\newpage
  }
\fi

\ifnum\WT@abstype>0
  \WT@dbgmsg{Setting frontmatter commands noops}
  \def\signaturepage{}
  \def\copyrightpage{}
  \newcommand{\makededication}[1][]{}
  \def\makeack{}
\else
  \def\signaturepage{
    \typeout{Signature Page}
    \bgroup
    \noindent
    Accepted by the Graduate Faculty, Indiana University, in partial
    fulfillment of the requirements for the degree of \check@val\@degree.
    \egroup
    \vskip.5in
    \hbox to\textwidth{\hfill\WT@sig{\check@val\@principaladvisor, Ph.D.}}%
    \hbox to\textwidth{\hfill\WT@sig{\check@val\@secondreader, Ph.D.}}%
    \hbox to\textwidth{\hfill\WT@sig{\check@val\@thirdreader, Ph.D.}}%
    \ifWT@three\else%
      \hbox to\textwidth{\hfill\WT@sig{\check@val\@fourthreader, Ph.D.}}%
    \fi%
    \ifx\@fifthreader\relax\else%
      \hbox to\textwidth{\hfill\WT@sig{\check@val\@fifthreader, Ph.D.}}%
    \fi
    \vfill
    \noindent\check@val\@submitdate
    \vfill
    \newpage
  }

  \def\copyrightpage{
    \typeout{Copyright Page}
    \hbox{}\vfill
    \begin{center}
    Copyright \check@val\@copyrightyear \\
    \check@val\@author \\
    ALL RIGHTS RESERVED
    \end{center}
    \vfill
    \newpage
  }

  \newcommand{\makededication}[1][1in]{
    \ifvoid\dedicationbox\else
    \typeout{Dedication}
    \hbox{}\vskip#1\unvbox\dedicationbox\vfill%
    \newpage
    \fi
  }


  \def\makeack{
    \ifvoid\acknowledgebox\else
    \typeout{Acknowledgements}
    \@makeschapterhead{Acknowledgements}
    \unvbox\acknowledgebox
    \newpage
    \fi
  }

\fi

\newcommand{\WT@sig}[2][3in]{
   \vbox{%
    \hrule width 0pt height 1in depth 0pt%
    \hrule width #1 height .4pt depth 0pt%
    \vskip2mm%
    \hbox to #1{\hfill #2}%
   }
}

\def\tableofcontents{
  \bgroup
  \renewcommand{\baselinestretch}{\WT@blstretch}
  \normalfont
  \@starttoc{toc}\contentsname
  \egroup
}
\def\listoffigures{
  \bgroup
  \renewcommand{\baselinestretch}{\WT@blstretch}
  \normalfont
  \@starttoc{lof}\listfigurename
  \egroup
}
\def\listoftables{
  \bgroup
  \renewcommand{\baselinestretch}{\WT@blstretch}
  \normalfont
  \@starttoc{lot}\listtablename
  \egroup
}

\def\frontmatter{\cleardoublepage\pagenumbering{roman}\pagestyle{plain}}

\def\mainmatter{
  \cleardoublepage
  \pagenumbering{arabic}
  \pagestyle{headings}
  \renewcommand{\baselinestretch}{\WT@blstretch}
  \normalfont
}

\def\backmatter{
  \newpage
  \pagestyle{empty}
  \renewcommand{\baselinestretch}{1}
  \normalfont
}

\def\check@val#1{%
  \ifx#1\relax%
    \typeout{}%
    \typeout{!!!!!!!!}%
    \typeout{Warning: #1 not set!}%
    \typeout{!!!!!!!!}%
    \hbox{???}%
  \else%
    #1%
  \fi%
}

\renewcommand{\seename}{see}

\def\WT@blstretch{1.67}
\ifnum\@mainsize=10\def\WT@blstretch{1.67}\fi
\ifnum\@mainsize=11\def\WT@blstretch{1.62}\fi
\ifnum\@mainsize=12\def\WT@blstretch{1.66}\fi
\WT@dbgmsg{Baseline stretch: \WT@blstretch}

\pagestyle{chapter}
\pagenumbering{arabic}
\normalsize



\endinput
%%
%% End of file `westhesis.cls'.
