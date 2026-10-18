English version: [README.md](README.md).

# groups — размерные подгруппы групп в Lean

Постановка задачи Коуровской тетради 20.84 — **верно ли $D_5(G) \subseteq \gamma_4(G)$ для всякой
группы $G$?** — в Lean 4 / Mathlib, с базовыми фактами, доказанными полностью, и сравнением с
лиевским случаем, который доказан и формализован в [IMP26] (arXiv:2610.02042, репозиторий
<https://github.com/TimmPeterson/lie-algebras>).

Lean `v4.29.0`, Mathlib `v4.29.0` (rev `8a17838`), та же версия, что у авторов. Пакет авторов
`lie-rings` подключён через `require` на проверенном коммите `ed3d9fb` (тот же, что в подмодуле
`upstream/lie-algebras`); нужен только файлу `LieComparison.lean`.

## Определения (`GroupDimension/Basic.lean`)

| В статье | В Lean |
|---|---|
| $\mathbb Z[G]$ | `MonoidAlgebra ℤ G` |
| $\varepsilon\colon \mathbb Z[G]\to\mathbb Z$, $g\mapsto 1$ | `augmentation G := (MonoidAlgebra.lift ℤ ℤ G 1).toRingHom` |
| $\Delta(G)=\ker\varepsilon$ | `augIdeal G := RingHom.ker (augmentation G)` — `Ideal`, с экземпляром `IsTwoSided` |
| $D_n(G)=\{g \mid g-1\in\Delta^n\}$ | `D n G : Subgroup G`, `mem_D` — по определению (`Iff.rfl`) |
| $\gamma_n(G)$, $\gamma_1=G$ | Mathlib `lowerCentralSeries G (n-1)` |

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
| **лемма 5.9 статьи** (центральный корень): $K=H\langle r\rangle$, $r$ централен, $|K:H|=m$, $r^m=g^m$ с $g\in H$ (не обязательно центральным) $\Rightarrow$ $\mathbb Z[H]\cap\Delta(K)^n=\Delta(H)^n$ при всех $n$ и $D_n(K)=D_n(H)$ при $n\ge2$ | `D_n_eq_of_index`; `CentralRoot.iota_mem_augIdeal_pow_iff`, `CentralRoot.D_eq` | `CentralRoot.lean` |
| **предложение 5.8(1) статьи**, $E=D_8$: $Q=H\circ D_8$ ($a,b$ — инволюции, перестановочные с $H$, $Q=H\langle a,b\rangle$, $a,b,ab\notin H$), $t=[a,b]\in\gamma_2(H)$ $\Rightarrow$ $\mathbb Z[H]\cap\Delta(Q)^n=\Delta(H)^n$ и $D_n(Q)=D_n(H)$ при $n\ge2$ | `D_n_eq_of_dihedral`; `DihedralData.iota_mem_augIdeal_pow_iff` | `CentralD8.lean` |
| центральный квадратный корень: $K=H\sqcup Hr$, $r$ централен, $c=g^{-2}r^2$, $c^{2^j}-1\in\Delta(H)^{j+2}$ $\Rightarrow$ $\mathbb Z[H]\cap\Delta(K)^n=\Delta(H)^n$, $D_n(K)=D_n(H)$ | `D_n_eq_of_sqrt` | `CentralSqrt.lean` |
| **предложение 5.8 статьи** целиком: $Q=H\circ E$, $E/Z(E)\cong(\mathbb Z/2)^2$ ($s=\alpha^2$, $\beta^2=s^e$, $t=[\alpha,\beta]\in\gamma_2(H)$, $c=g^{-2}s$, $c^{2^j}-1\in\Delta(H)^{j+2}$) $\Rightarrow$ $\mathbb Z[H]\cap\Delta(Q)^n=\Delta(H)^n$ и $D_n(Q)=D_n(H)$ при $n\ge2$ (для $Q$ в нормальной форме $H\sqcup H\alpha\sqcup H\beta\sqcup H\alpha\beta$); случаи $Q_8$, $M_{2^{k+2}}$ с $s=g^2$, с $s\in\gamma_2$, $s^2\in\gamma_3$, $s^4=1$ и с $c^{2^j}\in\gamma_{j+2}(H)$ | `D_n_eq_of_central_product`; `D_n_eq_of_quaternion`, `D_n_eq_of_modular_sq`, `D_n_eq_of_modular_comm`, `D_n_eq_of_central_product_of_gamma` | `CentralProduct.lean` |
| лиевский $D_5(L)\subseteq\gamma_4(L)$ (из `corollaryD` авторов) | `LieComparison.lieDimensionQuestion5` | `LieComparison.lean` |

$D_2 = \gamma_2$ доказано через тривиальное квадратично-нулевое расширение
$T=\mathbb Z\oplus G_{ab}$ (`TrivSqZeroExt`): $g\mapsto(1,\bar g)$ продолжается до кольцевого
$\Phi\colon\mathbb Z[G]\to T$ с первой координатой $\varepsilon$, поэтому $\Phi(\Delta^2)=0$ и
$\Phi(g-1)=(0,\bar g)$. Это та же идея, что у авторов в `DegreeTwo.lean` (квадратично-нулевое
представление).

`#print axioms` для всех 173 доказанных объявлений (`AxiomAudit.lean`) — только `propext`,
`Classical.choice`, `Quot.sound`. Ни `sorry`, ни `axiom` в исходниках нет.

## Только сформулировано (`def … : Prop`, без доказательства и без допущения)

Это **формулировки, не доказательства**: ни одна не объявлена как `axiom`, нигде не
предполагается. Ссылки — в docstring; данные, помеченные †, с оригиналом не сверены.

| `Prop` | Содержание | Литература |
|---|---|---|
| `DimensionQuestion5` | $\forall G,\ D_5(G)\subseteq\gamma_4(G)$ — **открытый вопрос** | Коуровская тетрадь 20.84 [KM26]; [IMP26, §1.3] |
| `DThreeEqGammaThree` | $D_3=\gamma_3$ | Higman, Rees (не опубл.), Passi [Pas68]†; [Pas79], [MP09] |
| `PassiDFourSquare` | $g\in D_4 \Rightarrow g^2\in\gamma_4$ | Passi [Pas68]† |
| `RipsExample` | $\exists G,\ D_4(G)\ne\gamma_4(G)$ | Rips [Rip72] |
| `TaharaDFiveExponentSix` | $g\in D_5 \Rightarrow g^6\in\gamma_5$ | Tahara [Tah81]†; [MP09] |
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
cd groups
lake exe cache get          # Mathlib из кэша
lake build                  # GroupDimension + нужная часть lie-rings
lake env lean AxiomAudit.lean
```

С нуля, кроме Mathlib из кэша, собирается пакет авторов — около 4 мин на 16 ядрах
(см. аудит, [`../notes/formalization-audit.ru.md`](../notes/formalization-audit.ru.md)).

## Литература

* [IMP26] V. Ionin, R. Mikhailov, T. Petrov, *Dimension subrings of Lie rings*, arXiv:2610.02042.
* [KM26] *The Kourovka notebook*, 21st ed., arXiv:1401.0300v46, Problem 20.84.
* [Rip72] E. Rips, Israel J. Math. 12 (1972), 342–346.
* [GK92] N. Gupta, Yu. V. Kuz'min, J. Pure Appl. Algebra 78 (1992), 165–172.
* [Pas79] I. B. S. Passi, *Group rings and their augmentation ideals*, LNM 715, 1979.
* [MP09] R. Mikhailov, I. B. S. Passi, *Lower central and dimension series of groups*, LNM 1952, 2009.
* [Pas68]† I. B. S. Passi, *Dimension subgroups*, J. Algebra 9 (1968), 152–182.
* [Tah81]† K.-I. Tahara, J. Algebra 71 (1981), 141–173.
* Quillen 1968† — D. Quillen, *On the associated graded ring of a group ring*, J. Algebra 10 (1968).
