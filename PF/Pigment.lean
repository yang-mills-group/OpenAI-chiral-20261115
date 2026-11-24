import PF.GP
set_option autoImplicit false
set_option maxHeartbeats 90000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
namespace PureForce.Boots
open BPress Pec Push.Local Push.AbsoluteSums Font Tenant
variable {n:Side}
local notation "G" => SU.group
local notation "S" n => More n
private abbrev bootlen (x:Site n)(j:Pec.Ok n) := (Nacre.boot (node x) j).length
private def orient (s:Signed) (x:Site n) := turnSites s (0:Site (S n)) (node x)
private lemma turned_cost {U V : Pane n}{δ:ℝ} (c:∀ i,BPress.chord (V i) (U i) ≤δ)(s:Signed):∀ i,BPress.chord ((Lattice.pull s (0:Site (S n)) V) i) ((pull s 0 U) i)≤δ:=by
 rintro ⟨x,j⟩; unfold Lattice.pull; cases hv:Lattice.Step.rotate (posDir j) s with|mk i t => cases t; exact c _; exact le_trans (chord.inv ..).le (c _) -- caution unused hv
-- `Yg` really signed pull. use bootLen (not diameter down to torus distance alone).
abbrev Key (n:Side) := Site n× Pec.Ok n × Pec.Ok n
def Key.length (i:Key n):=bootlen i.1 i.2.1 + bootlen i.1 i.2.2 + 2 -- so connected footprint card
private def ages (x:Site n)(a:Pec.Ok n) := Paths.native (node x) (Nacre.boot (node x) a)

def lands(s:Signed)(i:Key n): Support (S n):= ((ages i.1 i.2.1)∪ ages i.1 i.2.2).image (turnSites s (0:Site (S n)))

open BPress.Wealth
lemma flower (z:Key n) (s:Signed):
    orient s z.1∈lands s z ∧ Branch.Grove (Grid.field 4 (S n)) (lands s z) ∧ lands s z⊆Lattice.halo z.length {orient s z.1} ∧ (lands s z).card≤z.length:=by
  let f:=turnSites s (0:Site (S n)); let c:=node z.1; have hl(i): c∈ages z.1 i:= walks_first ..; refine ⟨Finset.mem_image_of_mem f (mem_union_left _ (hl z.2.1)), photo_g s _ ((walks_g c (Nacre.boot c z.2.1)).unite (walks_g c (Nacre.boot c z.2.2)) (hl _) (hl _)),fun i he=>?_, (Finset.card_image_le.trans ((Finset.card_union_le ..).trans ?_))⟩
  · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp he; apply halo_spec.mpr; refine ⟨orient s z.1,mem_singleton_self _,?_⟩; unfold orient; rw [turn_sep]; unfold Key.length
    rcases mem_union.mp hj with h | h
    · exact (Paths.to_ball _ _ h).trans (Nat.le_trans (Nat.le_add_right ..) (Nat.le_add_right ..)) -- invalid syntax ?
    exact (Paths.to_ball _ _ h).trans (Nat.le_trans (Nat.le_add_left ..) (Nat.le_add_right ..))
  have hp (i) : (ages z.1 i).card≤ bootlen z.1 i+1:=walks_n ..; exact (add_le_add (hp _) (hp _)).trans_eq (by unfold Key.length; omega)

private def theColor (U:Pane n)(s:Signed)(x:Site n)(i:Pec.Ok n):= silt (node x) i (Lattice.pull s (0:Site (S n)) U)

def pearl (P:Pride n)(s:Signed)(i:Key n)(U:Pane n):ℂ:=Pec.pays s (inner ℝ (theColor U s i.1 i.2.1) (theColor U s i.1 i.2.2) • P i.1 i.2.1 i.2.2)
lemma pearl_local (P:Pride n)(s:Signed)(i:Key n):LocalOn (lands s i) (pearl P s i):=by
  intro U V h; let l:=i.1; have he: Agrees (ages l i.2.1 ∪ ages l i.2.2:Finset _) (pull s 0 U) (pull s 0 V):=agrees_pull s 0 h
  have hx(j) (z:ages l j ⊆ (ages l i.2.1 ∪ ages l i.2.2:Finset _)) : theColor U s l j=theColor V s l j := congrArg (fun u=>SU.group.curvature u) (Lattice.travel_local (node l) (Nacre.boot (node l) j) _ _ (fun i e q=> he i (z (List.mem_toFinset.mpr e)) (z (List.mem_toFinset.mpr q))))
  unfold pearl; rw [show i.1= l from rfl,hx i.2.1 subset_union_left,hx i.2.2 subset_union_right]
variable {U V:Pane n}{δ:ℝ}(i:Key n)(P:Pride n)(s:Signed)
-- note taking V new W loom, U old W here in F2 but didn't need CapX.
private lemma norm_pays(x:ℂ): ‖Pec.pays s x‖=‖x‖:=by rw [complX]; unfold cSignX; split; exact Complex.norm_conj _; rfl -- cSignX which?
lemma pearl_change (k:∀ j,BPress.chord (V j) (U j) ≤ δ) :
    ‖pearl P s i V-pearl P s i U‖≤ 2 * i.length * δ * ‖P i.1 i.2.1 i.2.2‖ := by
  unfold pearl; rw [←map_sub,norm_pays,←sub_smul,norm_smul]; gcongr
  let w:=theColor V s i.1; let u:=theColor U s i.1
  have hp(j) (A:Pane n): ‖theColor A s i.1 j‖ ≤ 2:=(SU.group.curvature_norm _).trans (SU.group.chord_le_two _)
  have h(j:Pec.Ok n): ‖w j-u j‖ ≤ bootlen i.1 j*δ:= (Spin.curv_diff ..).trans (BPress.chord.path _ _ _ _ _ (fun b _ _=> turned_cost k s b))
  change ‖inner ℝ (w _) (w _) - inner ℝ (u _) (u _)‖ ≤ _
  rw [show inner ℝ (w i.2.1) (w i.2.2)-inner ℝ (u i.2.1) (u i.2.2)=inner ℝ (w i.2.1-u i.2.1) (w i.2.2)+inner ℝ (u i.2.1) (w i.2.2-u i.2.2) by rw [inner_sub_left,inner_sub_right]; ring]
  have ht: 0 ≤ δ:=(chord.positive (V (0, (0:Axis))) (U _)).trans (k _)
  refine (norm_add_le ..).trans ((add_le_add ((norm_inner_le_norm ..).trans (mul_le_mul (h _) (hp _ V) (norm_nonneg _) (by positivity))) ((norm_inner_le_norm ..).trans (mul_le_mul (hp _ U) (h _) (norm_nonneg _) (by norm_num)))).trans ?_)
  unfold Key.length; push_cast; linarith
abbrev Doc(n:Side):=Signed×Key n
private abbrev avg:ℝ:=(Fintype.card Signed:ℝ)⁻¹

def Doc.chip (P:Pride n) (U V:Pane n) (z:Doc n) := -avg • (pearl P z.1 z.2 V-pearl P z.1 z.2 U)
lemma assemble : ∑ z:Doc n,z.chip P U V=Pec.pigment P U-Pec.pigment P V:=by
  have he (U:Pane n):Pec.pigment P U = avg • (∑ z:Doc n,pearl P z.1 z.2 U):=by
    unfold Pec.pigment lexn; apply congrArg _; unfold Doc; rw [Fintype.sum_prod_type]; unfold Key; simp_rw [Fintype.sum_prod_type]; unfold pearl theColor zinger Pec.tag; simp_rw [map_sum, Nacre.Ywin]
  simp_rw [Doc.chip,neg_smul, smul_sub,Finset.sum_neg_distrib,Finset.sum_sub_distrib,← Finset.smul_sum]; rw [he,he]; abel

lemma touch (z:Doc n){e:gaugeLink n}(f:∀ i≠e,V i=U i)(t:z.chip P U V≠0) : e.1 ∈ lands z.1 z.2 ∧ e.1+step e.2∈lands z.1 z.2:=by
  by_contra! h; have hg:= pearl_local P z.1 z.2 V U (fun i g j=> f i (fun b=> h (b ▸ g) (b ▸ j))); apply t; rw [Doc.chip,hg,sub_self,smul_zero]
@[fun_prop] lemma chip_cont (z:Doc n): Continuous fun x:Pane n × Pane n=>z.chip P x.1 x.2:=by
 unfold Doc.chip pearl theColor silt; fun_prop

def rate(a:ℝ):= a/32
def overhead (a:ℝ):= Real.exp (rate a*36)*36

variable {a C:ℝ}(p:0<a)
include p
private def con(x:Site n)(j k:Pec.Ok n) := Font.contour (node x) j k
lemma linkFee (x:Site n)(j k:Pec.Ok n): let l:= ((show Key n from (x,j,k)).length:ℝ);
    2*l*Real.exp (rate a*l)*Real.exp (rate a*l)≤overhead a * nick a (con x j k):=by
  intro l; let D:=con x j k; have he (i:Pec.Ok n) :=Nacre.leanB (node x) i
  have hv: ((show Key n from (x,j,k)).length) ≤ 8*(dial (node x) j+dial (node x) k)+18:=by
    unfold Key.length bootlen; dsimp; have h:=he j; have ht:= he k; omega
  have hl: l≤8*D+18:=by unfold l D con contour; exact_mod_cast hv
  have hD:0≤D:=ct_pos ..; have ha:0<rate a:=by unfold rate; positivity
  change _≤ overhead a * nick a D
  calc
    _ = (2*l)*Real.exp ((rate a*l)+(rate a*l)):= by rw [Real.exp_add,mul_assoc]
    _ ≤ (36*(1+D))*Real.exp ((rate a*36)+a*D):=by
      apply mul_le_mul (by linarith) (Real.exp_monotone ?_) (Real.exp_pos _).le (by positivity)
      have hb:= mul_le_mul_of_nonneg_left hl ha.le
      unfold rate at *; nlinarith only [hb,mul_nonneg p.le hD]
    _ = _:=by rw [Real.exp_add]; unfold overhead Font.nick; ring

-- hit receipt: either zero or all include stored link, so with (orientation on both sides)
-- use decay in distance from the anchor.
lemma taxHit (z:Doc n){e:gaugeLink n}(f:∀ i≠e,V i=U i)(h:∀ i, BPress.chord (V i) (U i)≤δ) :
    let x:=z.2.1; let j:= z.2.2.1; let y:=z.2.2.2; let A:=Real.exp (-rate a*separation e.1 (orient z.1 x));
    ‖z.chip P U V‖ * Real.exp (rate a*z.2.length) ≤ A*(avg * (δ* overhead a) * (nick a (con x j y)*‖P x j y‖)):=by
  intro x j y A; have hv:0≤avg:=by unfold avg; positivity
  have hD:0≤δ:=(chord.positive ..).trans (h e)
  have hz:= linkFee (n:=n) p x j y; let d:= (z.2.length:ℝ); let m:= ‖P x j y‖
  change 2*d*Real.exp (rate a*d)*Real.exp (rate a*d) ≤ _ at hz
  have hr:= (nick_pos a (show 0≤ Font.contour (node x) j y from ct_pos ..)).le
  by_cases ht: z.chip P U V=0
  · rw [ht,norm_zero,zero_mul]; unfold overhead con A; positivity
  rw [Doc.chip,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg hv]
  have hy := halo_spec.mp ((flower z.2 z.1).2.2.1 ((touch P z f ht).1))
  obtain ⟨b,o,hy⟩:= hy
  let w:= (separation e.1 (orient z.1 x):ℝ)
  have hw:w ≤ d := by
    unfold w d x; rw [separation_comm]; exact_mod_cast Finset.mem_singleton.mp o ▸ hy -- syntax error prec cast?
  calc
    _ ≤ avg*(2*d*δ*m)* Real.exp (rate a*d) :=by gcongr; exact pearl_change z.2 P z.1 h
    _ = Real.exp (-(rate a*d)) * (avg*δ*(2*d * Real.exp (rate a*d)*Real.exp (rate a*d)) * m):= by rw [Real.exp_neg]; field_simp
    _ ≤ A*(avg*(δ*overhead a)*(nick a (con x j y)*m)):= by
      refine le_trans (mul_le_mul (show Real.exp (-(rate a*d)) ≤ A from Real.exp_monotone ?_) (show avg*δ*(2*d * _*_)*m ≤ _ from ?_) (show 0≤ avg*δ*(2*d * _*_)*m by unfold m d; positivity) (Real.exp_pos _).le) le_rfl -- parentheses of expression
      · have hh:= rate a; change _ ≤ -rate a * w; have hh:0 ≤ rate a:=by unfold rate; positivity
        nlinarith only [mul_le_mul_of_nonneg_left hw hh]
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz (mul_nonneg hv hD)) (norm_nonneg _)).trans_eq (by ring)

open UVNext.PricedKernels
variable (L:Lac P a C)
include L
def collation (a C:ℝ):= basin (rate a) * (overhead a*C)
lemma batches {e:gaugeLink n}(f:∀ i≠e,V i=U i)(h:∀ i, BPress.chord (V i) (U i)≤δ) :
    SumBudget (fun j:Doc n=> ‖Doc.chip P U V j‖ * Real.exp (rate a*j.2.length)) (collation a C*δ):=by
  have hw:0 < rate a:=by unfold rate; positivity
  have hc:0 ≤ C:= (Czero (n:=n) (node 0) (P 0) (a:=a)).trans (L.pay 0)
  have ht:0≤ avg:=by unfold avg; positivity
  have hu:0≤δ:= (chord.positive ..).trans (h e)
  have he:0≤overhead a:=by unfold overhead; positivity
  apply budget_finite (fun i=> by positivity)
  refine (sum_le_sum (fun i _=> taxHit P p i f h)).trans ?_
  unfold Doc; rw [Fintype.sum_prod_type]; unfold Key; simp_rw [Fintype.sum_prod_type]
  let g(i:Site (S n)):=Real.exp (-rate a*separation e.1 i)
  have hx(s:Signed): ∑ i:Site n,g (orient s i) ≤ basin (rate a):=by
    rw [←sum_image (by intro x _ y _ t; exact Tenant.needle ((turnSites s 0).injective t))]; exact (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>(Real.exp_pos _).le)).trans (funnel hw e.1)
  change ∑ s:Signed, ∑ x:Site n, ∑ j:Ok n,∑ i:Ok n, g (orient s x) * (avg * (δ*overhead a)*(nick a (con x j i)*‖P x j i‖)) ≤ _
  simp only [←mul_sum]; -- twice; rewrite inner using cents
  refine le_trans (sum_le_sum (g:=fun _=> avg*((basin (rate a))*(δ*overhead a*C))) fun s _=>?_ ) ?_
  · refine le_trans (sum_le_sum (g:=fun i=>g (orient s i)*(avg*(δ* overhead a)*C)) (fun i _=>?_)) ?_
    · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (L.pay i) (by positivity)) (Real.exp_pos _).le
    rw [←sum_mul]; exact (mul_le_mul_of_nonneg_right (hx s) (by positivity)).trans_eq (by ring)
  simp only [sum_const,nsmul_eq_mul,card_univ,←mul_assoc]; unfold avg; rw [mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)]; unfold collation; ring_nf; rfl
end PureForce.Boots
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
