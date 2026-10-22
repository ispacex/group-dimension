English version: [README.md](README.md).

# group-dimension — размерные подгруппы групп в Lean

[![CI](https://github.com/ispacex/group-dimension/actions/workflows/ci.yml/badge.svg)](https://github.com/ispacex/group-dimension/actions/workflows/ci.yml)

Lean-формализация к статье «Задача о $D_5$» (PDF:
[русская версия](https://ispacex.github.io/d5/paper/d5-ru.pdf), [английская](https://ispacex.github.io/d5/paper/d5.pdf);
сайт <https://ispacex.github.io/d5>). Вычисления, заметки и аудит формализации — в
<https://github.com/ispacex/dimension-subrings>, где этот пакет подключён подмодулем `groups/` (разрабатывался он там же; история
сохранена здесь).

## Подключение как зависимости

```toml
[[require]]
name = "group-dimension"
git = "https://github.com/ispacex/group-dimension"
rev = "main"
```

затем `import GroupDimension`.

Постановка задачи Коуровской тетради 20.84 — **верно ли $D_5(G) \subseteq \gamma_4(G)$ для всякой
группы $G$?** — в Lean 4 / Mathlib, с базовыми фактами, доказанными полностью, и сравнением с
лиевским случаем, который доказан и формализован в [IMP26] (arXiv:2610.02042, репозиторий
<https://github.com/TimmPeterson/lie-algebras>).

Lean `v4.29.0`, Mathlib `v4.29.0` (rev `8a17838`), та же версия, что у авторов. Пакет авторов
`lie-rings` подключён через `require` на проверенном коммите `ed3d9fb` (тот же, что в подмодуле
`upstream/lie-algebras` репозитория [dimension-subrings](https://github.com/ispacex/dimension-subrings)); нужен только файлу `LieComparison.lean`.

## Определения (`GroupDimension/Basic.lean`)

| В статье | В Lean |
|---|---|
| $\mathbb Z[G]$ | `MonoidAlgebra ℤ G` |
| $\varepsilon\colon \mathbb Z[G]\to\mathbb Z$, $g\mapsto 1$ | `augmentation G := (MonoidAlgebra.lift ℤ ℤ G 1).toRingHom` |
| $\Delta(G)=\ker\varepsilon$ | `augIdeal G := RingHom.ker (augmentation G)` — `Ideal`, с экземпляром `IsTwoSided` |
| $D_n(G)=\{g \mid g-1\in\Delta^n\}$ | `D n G : Subgroup G`, `mem_D` — по определению (`Iff.rfl`) |
| $\gamma_n(G)$, $\gamma_1=G$ | Mathlib `lowerCentralSeries G (n-1)` |
| $H^m$, подгруппа, порождённая $m$-ми степенями | `powSubgroup H m` |
| $P_n(G)$, нижний экспоненциально-$p$-центральный ряд: $P_1=G$, $P_{i+1}=[P_i,G]P_i^p$ | `expCentral p G n` (и $P_0=G$) |
| $M_n(G)=\prod_{ip^j\ge n}\gamma_i^{p^j}$ | `jennings p G n` — **формула Дженнингса–Лазара взята за определение**; её совпадение с $G\cap(1+\Delta_{\mathbb F_p}(G)^n)$ (определение статьи) — теорема Дженнингса. Её трудное включение доказано в нужном статье случае $p=2$, $n=5$, ступень $\le3$: $G\cap(1+\Delta_{\mathbb F_2}^5)\le$ `jennings 2 G 5` (`mem_jennings_of_sub_one_mem`, `Jennings/`); в общем виде оно доказано с рядом Лазара вместо произведения, а их совпадение (Лазар) не формализовано |
| кандидат (§5, перед леммой 5.6) | `IsCandidate Q n` (`Candidate.lean`) |

**Нумерация нижнего центрального ряда.** В Mathlib (`Mathlib/GroupTheory/Nilpotent.lean`)
`lowerCentralSeries G 0 = ⊤`, `lowerCentralSeries G (k+1) = ⁅lowerCentralSeries G k, ⊤⁆`,
поэтому **`lowerCentralSeries G k` = $\gamma_{k+1}(G)$**: $\gamma_2$ = `lowerCentralSeries G 1`
(= `commutator G`, `lowerCentralSeries_one`), $\gamma_4$ = `lowerCentralSeries G 3`. Нумерация
`D n G` — как в литературе, без сдвига ($D_0 = D_1 = G$).

**Коммутатор.** В Mathlib `⁅a, b⁆ = a b a⁻¹ b⁻¹`. Тождество в $\mathbb Z[G]$:
$[a,b]-1 = \bigl((a-1)(b-1)-(b-1)(a-1)\bigr)\,a^{-1}b^{-1}$. Для соглашения статьи
$[a,b]=a^{-1}b^{-1}ab$ — $[a,b]-1 = a^{-1}b^{-1}\bigl((a-1)(b-1)-(b-1)(a-1)\bigr)$, как в
постановке задачи. Оба тождества доказаны (`of_commutator_sub_one`,
`of_inv_mul_inv_mul_mul_sub_one`).

## Доказано в Lean (0 `sorry`)

| Утверждение | Объявление | Файл |
|---|---|---|
| $D_n(G)$ — нормальная подгруппа | `D_normal` (instance) | `Basic.lean` |
| $D_0(G) = D_1(G) = G$ | `D_zero`, `D_one` | `Basic.lean` |
| $D_n$ убывает | `D_antitone` | `Basic.lean` |
| $\Delta^i\Delta^j \subseteq \Delta^{i+j}$ | `mul_mem_augIdeal_pow` | `Basic.lean` |
| оба коммутаторных тождества | `of_commutator_sub_one`, `of_inv_mul_inv_mul_mul_sub_one` | `LowerCentral.lean` |
| $[D_i, D_j] \subseteq D_{i+j}$ | `commutator_mem_D`, `commutator_D_le` | `LowerCentral.lean` |
| $\gamma_n(G) \subseteq D_n(G)$, $n \ge 1$ | `lowerCentralSeries_le_D` (`lcs k ≤ D (k+1)`), `gamma_le_D` (`lcs (n-1) ≤ D n`) | `LowerCentral.lean` |
| функториальность $f(D_n(G)) \subseteq D_n(H)$ | `map_mem_D`, `map_D_le`, `D_le_comap` | `LowerCentral.lean` |
| $D_2(G) = \gamma_2(G)$ (полностью, оба включения) | `D_two`, `D_two_le_commutator` | `DTwo.lean` |
| для сюръекции $\gamma_k(H) \subseteq f(\gamma_k(G))$; $\gamma_k(G/\gamma_k G)=1$ | `lowerCentralSeries_le_map_of_surjective`, `lowerCentralSeries_quotient_eq_bot` | `Reduction.lean` |
| $D_n(G/N)=1 \Rightarrow D_n(G)\subseteq N$ | `D_le_of_D_quotient_eq_bot` | `Reduction.lean` |
| **сведение**: вопрос $D_5\subseteq\gamma_4$ ⇔ $D_5(Q)=1$ для всех $Q$ класса $\le 3$ | `forall_D_le_iff`, `dimensionQuestion5_iff` | `Reduction.lean` |
| конечная порождённость: $x\in D_n(G)$ ⇒ $x\in D_n(H)$, $H$ порождена конечным множеством | `finRep_of_mem`, `exists_closure_finset_mem_D` | `FiniteReduction.lean` |
| **предложение 2.1 статьи**: при теоремах Пасси ($D_4^2\subseteq\gamma_4$) и Грюнберга (гипотезы) вопрос $D_5\subseteq\gamma_4$ ⇔ $D_5(Q)=1$ для всех конечных $2$-групп $Q$ класса $\le3$; при $D_3=\gamma_3$ (гипотеза) — класса ровно $3$ | `dimensionQuestion5_iff_finite_two_groups`, `dimensionQuestion5_iff_class_three` | `FiniteReduction.lean` |
| **замечание 2.3** (ограниченный вариант): при теореме Пасси (гипотеза) $D_5(Q)=1$ для $2$-групп класса $\le3$ порядка $\le2^k$ ⇒ $D_5(G)\subseteq\gamma_4(G)$ для конечных $G$ с силовской $2$-подгруппой порядка $\le2^k$; при $D_3=\gamma_3$ (гипотеза) — класса ровно $3$ | `D_five_le_of_bounded`, `D_five_le_of_bounded_class_three`, `exists_sylow_two_proj` | `FiniteReduction.lean` |
| $[\gamma_i,\gamma_j]\subseteq\gamma_{i+j}$; тождество Холла–Витта | `commutator_lcs_le`, `hall_witt` | `ClassFour.lean` |
| **лемма 6.3 статьи**: $p$ нечётно, $\vert\gamma_3/\gamma_4\vert=p$, $\gamma_2/\gamma_3$ порождается не более чем двумя элементами $\Rightarrow$ $[\gamma_2,\gamma_2]\subseteq\gamma_5$ (метабелевость при классе $\le4$); циклический случай без условия на $\gamma_3/\gamma_4$ | `commutator_gamma_two_le_gamma_five`, `metabelian_of_class_four`, `commutator_gamma_two_le_gamma_five_of_cyclic` | `ClassFour.lean`, `ClassFourOrder.lean` |
| **предложение 6.5 статьи**: $p$ нечётно, $Q$ — $p$-группа класса $\le4$, $Q''\ne1$ $\Rightarrow$ $d(Q)\ge3$, $\vert Q\vert\ge p^{d(Q)+5}$; отсюда (1) метабелевость при $\vert Q\vert\le p^7$ или $\vert Q\vert=p^8$, $d(Q)\ge4$; (2) при $p^9$: $d(Q)\in\{3,4\}$, тип $(4,3,1,1)$ или $(4,2,2,1)$ при $d=4$ | `card_ge_of_not_metabelian`, `metabelian_of_card_le`, `rank_of_card_nine`, `type_of_card_nine` | `ClassFourOrder.lean` |
| $p$-группа порядка $\le p^n$ порождается $n$ элементами; $H\gamma_2=G\Rightarrow H=G$ в конечной $p$-группе; $G=\langle x,y\rangle\Rightarrow\gamma_2=\langle[x,y]\rangle\gamma_3$ | `exists_generators_card_le`, `eq_top_of_sup_commutator`, `gamma_two_mod_of_pair` | `ClassFourOrder.lean` |
| **теорема 6.1 Тахары** [Tah81] (включение $\subseteq$): для конечной группы класса $\le4$ и любого базиса единственности с его структурными константами $D_5$ лежит в подгруппе, порождённой элементами $g(u,v,w)$ по целым наборам с условиями (A)–(F) | `taharaFiveOne : TaharaFiveOne` | `TaharaTheorem.lean`, `TaharaProof/` |
| её доказательство, по Тахаре: рамки (склеенные базисы единственности слоёв, нормальные формы), базис $\mathbb Z[G]$ из базисных произведений и $\Delta^n$ по модулю младших; $D_3=\gamma_3$ для таких групп (теорема 4.1); отображение $\psi_3$ теоремы 5.1 с базисом Лоузи в $W_3^*\oplus W_4$, $\psi_3(\Delta^5)\subseteq R_5^*$; расшифровка координат в (A)–(F) и $g=g(u,v,w)$ | `TaharaProof.Frame.basis`, `TaharaProof.Frame.D_three_le`, `TaharaProof.Frame.rel3_of_mem_Sp5`, `TaharaProof.Frame.S_mem_R5`, `TaharaProof.admissible_tau`, `TaharaProof.eq_gen` | `TaharaProof/` |
| **теорема 6.6 статьи**: $G/\gamma_2(G)$ конечна и имеет экспоненту $3$ $\Rightarrow$ $D_5(G)=\gamma_5(G)$; для конечной $Q$ класса $\le4$: $D_5(Q)=1$ (доказана из теоремы 6.1 Тахары как гипотезы, гипотеза затем снята) | `D_five_eq_gamma_five_of_exp_three`, `D_five_eq_bot_of_class_four_exp_three`; с гипотезой `TaharaFiveOne`: `ExpThree.D_five_eq_gamma_five`, `ExpThree.D_five_eq_bot_of_class_four` | `TaharaTheorem.lean`, `ExpThree.lean` |
| вычисление в её основе: в базисе единственности, согласованном с кубическим отображением, все образующие теоремы 6.1 Тахары тривиальны; $G/\gamma_2$ конечна $\Rightarrow$ $G/\gamma_k$ конечна | `ExpThree.Setup.gen_eq_one`, `ExpThree.finite_quotient_lcs` | `ExpThree.lean` |
| **теорема 6.8 статьи**: $G/\gamma_2(G)$ — конечная $3$-группа с циклической подгруппой кубов ($\cong C_{3^a}\times C_3^{s-1}$) $\Rightarrow$ $D_5(G)=\gamma_5(G)$; тождества $[x^9,y]=[x,y]^9$, $[x^{27},y]=1$, $[b,x^9]=1$ ($b\in\gamma_2$) в классе $\le4$ | `D_five_eq_gamma_five_of_cubes_cyclic`, `D_five_eq_bot_of_class_four_cubes_cyclic`; с гипотезой `TaharaFiveOne`: `ExpThree.D_five_eq_gamma_five_cyclic`, `ExpThree.D_five_eq_bot_of_class_four_cyclic`, `ExpThree.Setup8.gen_eq_one`; `ExpThree.tc_pow_nine'`, `ExpThree.tc_pow_27`, `ExpThree.tc_L1_pow_nine` | `TaharaTheorem.lean`, `ExpThreePlus.lean` |
| **лемма 5.9 статьи** (центральный корень): $K=H\langle r\rangle$, $r$ централен, $|K:H|=m$, $r^m=g^m$ с $g\in H$ (не обязательно центральным) $\Rightarrow$ $\mathbb Z[H]\cap\Delta(K)^n=\Delta(H)^n$ при всех $n$ и $D_n(K)=D_n(H)$ при $n\ge2$ | `D_n_eq_of_index`; `CentralRoot.iota_mem_augIdeal_pow_iff`, `CentralRoot.D_eq` | `CentralRoot.lean` |
| **предложение 5.8(1) статьи**, $E=D_8$: $Q=H\circ D_8$ ($a,b$ — инволюции, перестановочные с $H$, $Q=H\langle a,b\rangle$, $a,b,ab\notin H$), $t=[a,b]\in\gamma_2(H)$ $\Rightarrow$ $\mathbb Z[H]\cap\Delta(Q)^n=\Delta(H)^n$ и $D_n(Q)=D_n(H)$ при $n\ge2$ | `D_n_eq_of_dihedral`; `DihedralData.iota_mem_augIdeal_pow_iff` | `CentralD8.lean` |
| центральный квадратный корень: $K=H\sqcup Hr$, $r$ централен, $c=g^{-2}r^2$, $c^{2^j}-1\in\Delta(H)^{j+2}$ $\Rightarrow$ $\mathbb Z[H]\cap\Delta(K)^n=\Delta(H)^n$, $D_n(K)=D_n(H)$ | `D_n_eq_of_sqrt` | `CentralSqrt.lean` |
| **предложение 5.8 статьи** целиком: $Q=H\circ E$, $E/Z(E)\cong(\mathbb Z/2)^2$ ($s=\alpha^2$, $\beta^2=s^e$, $t=[\alpha,\beta]\in\gamma_2(H)$, $c=g^{-2}s$, $c^{2^j}-1\in\Delta(H)^{j+2}$) $\Rightarrow$ $\mathbb Z[H]\cap\Delta(Q)^n=\Delta(H)^n$ и $D_n(Q)=D_n(H)$ при $n\ge2$ (для $Q$ в нормальной форме $H\sqcup H\alpha\sqcup H\beta\sqcup H\alpha\beta$); случаи $Q_8$, $M_{2^{k+2}}$ с $s=g^2$, с $s\in\gamma_2$, $s^2\in\gamma_3$, $s^4=1$ и с $c^{2^j}\in\gamma_{j+2}(H)$ | `D_n_eq_of_central_product`; `D_n_eq_of_quaternion`, `D_n_eq_of_modular_sq`, `D_n_eq_of_modular_comm`, `D_n_eq_of_central_product_of_gamma` | `CentralProduct.lean` |
| **лемма 5.6 статьи**: нет кандидата $Q$ порядка $2^{11}$ с $Q/P_3(Q)\cong\mathbb Z/4\times(\mathbb Z/2)^7$; ряд $P_n$ нормален и убывает | `not_isCandidate_of_quotient_z4`; `expCentral_normal`, `expCentral_antitone`, `expCentral_succ` | `Candidate.lean` |
| **предложение 5.7 статьи** (в форме MATH-320): нет кандидата $Q$ порядка $2^{11}$ ранга $d(Q)\ge8$; доказательство элементарное, без классификации групп порядка $2^9$ ранга $8$ и без компьютера. Попутно: $P_2$ лежит в каждой максимальной подгруппе конечной $p$-группы, поэтому $d(G)\le n$ при $\vert G/P_2\vert\le p^n$; $\gamma_k\le P_k$; $P_k$ строго убывает до $1$ | `not_isCandidate_of_rank`; `false_of_card_expCentral_two_le` (у всякого кандидата $\vert P_2\vert\ge16$, т.е. $\vert\Phi(Q)\vert\ge16$); `false_of_gamma_two_le` (ядро леммы 5.6: $\gamma_2\le P_3$ невозможно для кандидата с $\vert P_3\vert=4$, $P_4=\langle n\rangle$); `rank_le_of_index_expCentral_two`, `expCentral_two_le_of_isCoatom`, `pow_mem_of_isCoatom`, `lowerCentralSeries_le_expCentral`, `expCentral_lt` | `Candidate.lean` |
| **теорема Дженнингса**, трудное включение (D5-32): для конечной $p$-группы и всякого ограниченного N-ряда $S$ ($[S_a,S_b]\le S_{a+b}$, $S_a^p\le S_{pa}$) $G\cap(1+\Delta_{\mathbb F_p}(G)^n)\le S_n$, через базис Дженнингса $\prod(x_i-1)^{a_i}$ алгебры $\mathbb F_p[G]$; ряд Лазара (наименьший такой) доходит до $1$; при $p=2$ и ступени $\le3$ $S_5\le G^8\gamma_2^4\gamma_3^2$ | `Jennings.RestrictedSeries.mem_of_sub_one_mem`, `mem_lazard_of_sub_one_mem`, `lazard_le_of_restrictedSeries`, `lazard_eventually_bot`, `ClassThree.lazard_five_le_jennings`, `mem_jennings_of_sub_one_mem`; через $\mathbb Z[G]\to\mathbb F_p[G]$: $D_5(G)\le G^8\gamma_2^4\gamma_3^2$ (`D_five_le_jennings`) | `Jennings/` |
| лиевский $D_5(L)\subseteq\gamma_4(L)$ (из `corollaryD` авторов) | `LieComparison.lieDimensionQuestion5` | `LieComparison.lean` |

$D_2 = \gamma_2$ доказано через тривиальное квадратично-нулевое расширение
$T=\mathbb Z\oplus G_{ab}$ (`TrivSqZeroExt`): $g\mapsto(1,\bar g)$ продолжается до кольцевого
$\Phi\colon\mathbb Z[G]\to T$ с первой координатой $\varepsilon$, поэтому $\Phi(\Delta^2)=0$ и
$\Phi(g-1)=(0,\bar g)$. Это та же идея, что у авторов в `DegreeTwo.lean` (квадратично-нулевое
представление).

`#print axioms` для всех 1332 доказанных объявлений (`AxiomAudit.lean`) — только `propext`,
`Classical.choice`, `Quot.sound`. Ни `sorry`, ни `axiom` в исходниках нет.

## Только сформулировано (`def … : Prop`, без доказательства)

Это **формулировки, не доказательства**: ни одна не объявлена как `axiom`, глобально ничего не
предполагается. Некоторые входят явными гипотезами в теоремы (`FiniteReduction.lean`:
`PassiDFourSquare`, `GruenbergResidualTwo`, `DThreeEqGammaThree`). `TaharaFiveOne`
(`Tahara.lean`) стоит здесь как утверждение из литературы, но оно доказано (`TaharaTheorem.lean`). Ссылки — в docstring; данные, помеченные †, с оригиналом не сверены.

| `Prop` | Содержание | Литература |
|---|---|---|
| `DimensionQuestion5` | $\forall G,\ D_5(G)\subseteq\gamma_4(G)$ — **открытый вопрос** | Коуровская тетрадь 20.84 [KM26]; [IMP26, §1.3] |
| `DThreeEqGammaThree` | $D_3=\gamma_3$ | Higman, Rees (не опубл.), Passi [Pas68]†; [Pas79], [MP09] |
| `PassiDFourSquare` | $g\in D_4 \Rightarrow g^2\in\gamma_4$ | Passi [Pas68]† |
| `RipsExample` | $\exists G,\ D_4(G)\ne\gamma_4(G)$ | Rips [Rip72] |
| `GruenbergResidualTwo` | к.п. нильпотентная $G$, никакая нечётная степень $g$ не равна $1$ $\Rightarrow$ $g\ne1$ в некоторой конечной $2$-фактор-группе | Gruenberg [Gru57] |
| `TaharaDFiveExponentSix` | $g\in D_5 \Rightarrow g^6\in\gamma_5$ | Тахара [Tah81, сл. 6.11]; [MP09] |
| `TaharaFiveOne` (`Tahara.lean`) | описание $D_5$ у Тахары для конечных групп класса $\le4$: $D_5$ лежит в подгруппе, порождённой элементами $g(u,v,w)$ по целым наборам с условиями (A)–(F), для любого базиса единственности с его структурными константами (сверено со сканом, с. 143, 150, 159–161; условие (C₂) повторно сверено с с. 160 после исправления опечатки в MATH-226) — **доказано**: `taharaFiveOne` | Тахара [Tah81, т. 6.1] |
| `GuptaKuzminAbelian` | $[D_n,D_n]\subseteq\gamma_{n+1}$ | [GK92], цит. по [IMP26, §1.2] |
| `GuptaKuzminDFourCentral` | $[D_4,G]=\gamma_5$ | [GK92], цит. по [IMP26, §1.2] |
| `LieComparison.FifthDimensionSquare` | $g\in D_5 \Rightarrow g^2\in G''\gamma_5$ | [MP09, Thm 2.28], цит. по [IMP26, §3.3] |
| `LieComparison.GroupCorollaryD c` | $D_{2c-1}\subseteq\gamma_{c+1}G''$ — групповой аналог Corollary D | статус при $c\ge4$ нам неизвестен |
| `LieComparison.GroupTheoremC c` | метабелева класса $\le c$ ⇒ $D_{2c-1}=1$ | аналог Theorem C, без утверждения об истинности |

## Сравнение с кольцами Ли (`LieComparison.lean`)

Файл импортирует `LieRings.Publication.Results`, ставит рядом лиевскую и групповую
постановки (`LieDimensionQuestion5` — доказано из `corollaryD`; `DimensionQuestion5` — открыто)
и в комментарии разбирает, какие шаги §§5–6 статьи переносятся. Кратко:

* **переносятся**: переход к фактору (Corollary 6.14; для групп доказано здесь —
  `dimensionQuestion5_iff`), сведение к конечно порождённым (Lemma 6.13), конструкция
  центрального расширения $T = G\times_{G_{ab}}P$ (но $T'\to T\to P$ расщепляется как
  полупрямое, а не прямое произведение);
* **прямого аналога нет**: PBW-фильтрации $P_{\le r}U(T)$ с $\mathrm{gr}\cong\mathrm{Sym}$ и
  базисом упорядоченных мономов (Thm 2.3, Cor 2.4); аддитивных ретракций
  $p\colon U(T)\to P_{\le2}U(T)$ и $r\colon P_{\le2}U(T)\to T$ (Thm 5.1, Lemma 5.3), которые
  держатся на том, что $T\subset U(T)$ — аддитивная подгруппа: у групп вложение
  $g\mapsto g-1$ аддитивно лишь по модулю $\Delta^2$; явного $\mathbb Z$-описания
  $\Delta(T)^n$, на котором строится ретракция $p$ (Prop. 6.12).

## Сборка

```bash
lake exe cache get          # Mathlib из кэша
lake build                  # GroupDimension + нужная часть lie-rings
lake env lean AxiomAudit.lean
```

С нуля, кроме Mathlib из кэша, собирается пакет авторов — около 4 мин на 16 ядрах
(см. аудит, [`notes/formalization-audit.ru.md`](https://github.com/ispacex/dimension-subrings/blob/main/notes/formalization-audit.ru.md) в dimension-subrings).

## Литература

* [IMP26] V. Ionin, R. Mikhailov, T. Petrov, *Dimension subrings of Lie rings*, arXiv:2610.02042.
* [KM26] *The Kourovka notebook*, 21st ed., arXiv:1401.0300v46, Problem 20.84.
* [Rip72] E. Rips, Israel J. Math. 12 (1972), 342–346.
* [GK92] N. Gupta, Yu. V. Kuz'min, J. Pure Appl. Algebra 78 (1992), 165–172.
* [Pas79] I. B. S. Passi, *Group rings and their augmentation ideals*, LNM 715, 1979.
* [MP09] R. Mikhailov, I. B. S. Passi, *Lower central and dimension series of groups*, LNM 1952, 2009.
* [Pas68]† I. B. S. Passi, *Dimension subgroups*, J. Algebra 9 (1968), 152–182.
* [Gru57] K. W. Gruenberg, Proc. London Math. Soc. (3) 7 (1957), 29–62.
* [Tah81] K.-I. Tahara, J. Algebra 71 (1981), 141–173.
* Quillen 1968† — D. Quillen, *On the associated graded ring of a group ring*, J. Algebra 10 (1968).
