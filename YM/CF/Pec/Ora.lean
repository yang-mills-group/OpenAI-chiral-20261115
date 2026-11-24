import YM.CF.Pec.Routine
import YM.AnalyticNext.CUBIC_MATCH.Handover
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n X m A L B :Side}{j k w:ℕ}{ho:Odd L.val} {Y:Pricing j L ho (Thread j)}{e d b a r:ℝ}{P:Grasp Y B e}
variable {G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B}{F: Forest T.ratio}{z:Vox m B→ AxisChart group F}
variable (H:Hull j L ho a b d e k m A B G T F z Y P)
lemma den_r {X:Aim n}{l a m b:ℝ}(p:Aim.toll X l m a b):Ample X.den:= amp_plus (amp_P _ (by omega) p.1.1 p.1.2.1) (amp_P _ (by omega) p.2.1 p.2.2.1)
lemma pullPay (L:Side)(ho:Odd L.val)(x a y b:ℝ)(p:0<x)(u:0<a)(v:0<y)(g:0<b)(k:ℕ):∃ s c:ℝ,0<s∧0<c∧∀ {m A B:Side}{G:Ratio (CSide m B) (CSide A B)}{T:Roam m A B}(F:Forest T.ratio), T.ratio=ratio G→ G.count=L→ ∀ U:Aim (CSide A B), U.toll x y a b→ ReadY F G (fun i=> foot G (U.den (fine group F i))) s c k:=by
 obtain ⟨j,V,h,t,H⟩:=skyK x a L p u 1 k; obtain ⟨l,M,hl,hM,Q⟩:= skyK y b L v g 2 k; refine ⟨_,_,lt_min h hl, add_pos t hM, fun {m A B G T} F ht hg U e=>?_⟩
 exact ((((H F G ht hg ho).1 U.x e.1.2.2).drop (min_le_left ..)).opP (((Q F G ht hg ho).1 U.y e.2.2.2).drop (min_le_right ..))) -- foot_add defeq
lemma monk (i:Orig n)(X:Dues n)(p:b≤ a): cents i X b≤ cents i X a:= Finset.sum_le_sum fun j _=> sum_le_sum fun k _=>mul_le_mul_of_nonneg_right (by unfold nick; have h:=ct_pos i j k; gcongr) (norm_nonneg _)
abbrev secondM (c:RG.Clip)(W:RG.PathData group)(u:Cloud n):ℂ:= ↑(secondTerm c W (represent u))
lemma sane {i j k:ℝ}{W:RG.PathData group}{q:RG.Clip}(Q:W.Bounds q i j k):ContDiffAt ℝ ω (secondM (n:=n) q W) 0:= Complex.ofRealCLM.contDiff.contDiffAt.comp _ (CubicMatch.aware Q).analytic
section
variable {n N:Side}{T:RG.StepData (More n) (More N)}{F:Forest T.ratio}{z:Cloud n →AxisChart group F}
lemma pane (h:Nativity F z)(W:Pride N):ContDiffAt ℝ ω (pigment W ∘ baby F z) 0:=by
 let f:= Iteration.chartOf F z; exact (((show ContDiffAt ℝ ω (pigment W ∘ represent) (f 0) by rw [show f 0=0 from h.icicle]; exact tuck W).comp _ h.kala)).congr_of_eventuallyEq (h.foldM.mono fun i (hi:baby F z i=_)=> congrArg (pigment W) hi) -- direction
end
structure Lac (D:Pride n)(a b:ℝ):Prop where
 lead:WordK D
 code:merit D
 pay(i):cents (node i) (D i) a≤ b
lemma strobe {X Z:Pride n}(p:WordK X)(v:WordK Z):WordK (X+Z):=fun i t a b=> congrArg₂ (· + ·) (p i t a b) (v i t a b)
lemma rockP {x v A:ℝ} (p:0<x)(h:0<v)(g:0<A)(L:Side)(u:2*A*v≤ Real.sqrt (L.val:ℝ)): (x + (2*A*x) * v / Real.sqrt L.val)*A ≤ 2*A*x:=by
 let D:= (Real.sqrt (L.val:ℝ)); have he: 0<D:=by unfold D; positivity
 have hp:(2*A*x)*v/D ≤ x:=by apply (div_le_iff₀ he).mpr; exact (mul_le_mul_of_nonneg_left u p.le).trans_eq rfl|>.trans' (le_of_eq (by ring))
 apply (mul_le_mul_of_nonneg_right (add_le_add_right hp _) g.le).trans_eq; ring
variable (G F z) in
def myth (q:RG.Clip) (W:RG.PathData group)(P:Grasp Y B e)(M:Male)(U:Dress (CSide A B))(I:Pride (CSide A B))(T':Pride (CSide m B))(α:ℝ)(x:Vox m B):ℂ:= pigment I (baby F z x)+ deflate (lush G P M U∘ ears F z) x- α • secondM q W x-pigment T' (represent x)
lemma ulster {β α v B C:ℝ} (p:0<β)(v0:0<v)(u:0≤α)(x:0<B)(f:0<C):∃ N:ℕ,∀ (L:Side)(h:Odd L.val), N≤L.val →  ∀ {k j:ℕ}{a b d e:ℝ}{Y:Pricing j L h (Thread j)}{B':Side}{P:Grasp Y B' e}(K:Pearl P),Stamped j L h Y → Spack j L h a b d k → 0<a → 0<b → 0<d → 0<e → 1≤j → ∀ r s i l k' j':ℝ,0<r → 0<s → 0< i → 0<l → 0<k' → 0<j' → ∃ c V z:ℝ,0<c∧0<V∧0<z ∧∃ n:ℕ,∀ {m A: Side}{G:Ratio (CSide m B') (CSide A B')}{T:Roam m A B'} {F:Forest T.ratio} {y:Vox m B' → AxisChart group F}{U:RG.PathData group}{q:RG.Clip}{H:Bed}{σ η t d' m':ℝ},Hull j L h a b d e k m A B' G T F y Y P → U.Bounds q σ η t → Floor H q (More (CSide m B')) d' m' →  H.metric.strip B C →  Attached H U →  Bid.Sworn H (More (CSide m B')) group → n ≤ (More (CSide m B')).val  →  Horizon F y 2 r s →  Gazes T F y β α v → ∀ M:Male,∀ A:Aim (CSide A B'),A.toll i k' l j' → ∀ I:Pride (CSide _ B'),Lac I c V → ∃ Q:Pride (CSide m B'), Lac Q c V∧∃ t':ℝ, |t'|≤z ∧cFoot 3 (myth G F y q U P M A.den I Q t'):=by
 obtain ⟨V,hv,D⟩:= stigma p v0 α u; let R:= momentBill B C; have ht:=oxygen x f; obtain ⟨N,hN⟩:=exists_nat_gt ((2*R*V)^2)
 refine ⟨max 4 N,fun L h g {k j a b d e Y B' P} K w W hA hB hD hE hP r s i l k' j' hu hk hi hl hs hx =>?_⟩
 obtain ⟨e,J,h',hJ,T⟩:=pullPay L h i l k' j' hi hl hs hx 2
 obtain ⟨x',g',hr,hy,F⟩:=ink_w K w W hA hB hD hE hP h' hJ hu hk
 let a:= min x' (min (B/2) (β/2)); have hq:0<a:=lt_min hr (lt_min (half_pos x) (half_pos p)); obtain ⟨j,X⟩:=D L h ((le_max_left ..).trans g) a hq ((min_le_right ..).trans (min_le_right ..))
 let A':=2*R*g'; let v':= g'+A'*V/(Real.sqrt (L.val:ℝ)); have hx:2*R*V≤ Real.sqrt (L.val:ℝ):=by nlinarith only [(show (2*R*V)^2≤(L.val:ℝ) from hN.le.trans (by exact_mod_cast (le_max_right 4 N).trans g)), (Real.sqrt_nonneg (L.val:ℝ)), Real.sq_sqrt (show 0≤(L.val:ℝ) from Nat.cast_nonneg _)]
 have hA':0<A':=by unfold A' R; positivity
 have hv':0<v':=by unfold v'; positivity
 have hl:0≤lime:=norm_nonneg _
 refine ⟨a,A',1+lime*v',hq,hA',(by positivity),j,fun {m A G T' F' y U q H σ η t d' m'} Hh ρ ω' Δ Yt φ' ψ rX τ M Q Q' I I'=>?_⟩
 obtain ⟨it,S,hS,hZ,hT⟩:= F Hh rX M Q.den (den_r Q') (T F' Hh.alignT Hh.fromL Q Q')
 obtain ⟨Yv,hY,hU,hV⟩:= X Hh.fromL Hh.alignT Hh.native τ ψ I I'.lead I'.code A' I'.pay
 let P':= S+ Yv; have he:WordK P':=strobe hS hY
 have hc(x): cents (node x) (P' x) a≤ v':=(coverG ..).trans (add_le_add (le_trans (monk _ _ (min_le_left ..)) (hT x)) (hV x)); obtain ⟨pM,hM⟩:= wagesP hc Δ x hq.le ((min_le_right ..).trans (min_le_left ..)) hv'.le f; let V':=drain P' H
 let z:=flag P'/8
 refine ⟨V',⟨drain_p he,minty_m he ω' Δ x,fun x=> (hM x).trans (rockP hy hv ht L hx)⟩,z,by unfold z; rw [abs_div,abs_of_pos (by norm_num:0<(8:ℝ))]; linarith [mul_nonneg hl hv'.le],?_⟩
 apply nextF (m:=2) ((((pane Hh.native I|>.of_le le_top).add it).sub ((sane ρ|>.of_le le_top).const_smul z)).sub ((tuck V').of_le le_top))
 intro x; have hp:= (toned (d:=0) ρ ω' Yt φ' x).const_smul z
 have hh:= (((hU x).add (hZ x)).sub hp).sub (zpark V' x); have hx:=minty_p (W:=P') φ' x; rw [show diem V' _= _ from hx,show diem P'=diem (S+Yv) from rfl,stemR,Pi.add_apply] at hh
 let Q0:=(↑(Bid.gaugeFiscal H x x):ℂ); rw [show diem Yv x+ diem S x-z • (↑(Bid.gaugeFiscal H x x/2):ℂ)-(diem S x+ diem Yv x-(flag P'/16) • Q0)=0 from ?_] at hh; apply hh.congr; intro i; simp only [myth, Function.comp_apply, smul_sub, smul_add]; rw [smul_comm z]
 unfold z Q0; simp only [Complex.real_smul, Complex.ofReal_div,Complex.ofReal_ofNat]; ring
end YM.CF.Pec
