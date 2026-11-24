import PF.Links
import PF.Bare
set_option autoImplicit false
set_option maxHeartbeats 380000
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

-- Physical gating on a single LP satellite
namespace PureForce
open Lattice
variable {N : Side}
-- Gauge not restricted unless required. biinvariance estimates including inverse links
open Gauge
variable {G : Gauge}
private abbrev Ch (x y : G.El) := G.chord (y*x⁻¹)
set_option maxHeartbeats 40000
private lemma ch_comm (x y : G.El) : Ch x y= Ch y x := by unfold Ch; rw [← G.chord_inv (y*x⁻¹),mul_inv_rev,inv_inv]
private lemma shift_ch (u v a b : G.El) : Ch (u*v) (a*b) ≤ Ch u a + Ch v b := by
  unfold Ch
  rw [mul_inv_rev,show a*b*(v⁻¹*u⁻¹)=(a*u⁻¹)*(u*(b*v⁻¹)*u⁻¹) by group]
  simpa only [G.chord_conj] using G.chord_triangle (a*u⁻¹) (u*(b*v⁻¹)*u⁻¹)
private lemma ch_inv (x y : G.El) : Ch x⁻¹ y⁻¹= Ch x y := by
  rw [ch_comm]; unfold Ch; rw [inv_inv,show x⁻¹*y=x⁻¹*(y*x⁻¹)*(x⁻¹)⁻¹ by group,G.chord_conj]
private lemma ch_bound (x y : G.El) : G.chord x ≤ G.chord y + Ch x y := by
  rw [ch_comm]; unfold Ch; convert G.chord_triangle (x*y⁻¹) y using 1
  · group
  rw [add_comm]

variable {U V : Config G (More N)}{δ:ℝ}
private lemma travel_ch (h:∀ e, Ch (U e) (V e) ≤ δ)(x:Skye.Seat N)(k:Lattice.Walk):
    Ch (Lattice.travel U x k) (Lattice.travel V x k) ≤ k.length * δ := by
  induction k generalizing x with
  | nil=> simp only [Lattice.travel, Ch, inv_one, one_mul, Gauge.chord_one, List.length_nil, Nat.cast_zero, zero_mul,le_refl]
  | cons i k e=>
    have he: Ch (i.read U x) (i.read V x) ≤ δ := by
      simp only [Lattice.Step.read]; split_ifs
      · rw [ch_inv]; exact h _
      apply h
    simp_rw [Lattice.travel,List.length_cons,Nat.cast_add,Nat.cast_one]
    apply (shift_ch ..).trans ((add_le_add he (e _)).trans_eq (by ring))

section single
local notation "ch" => SU.group.chord
variable {e : gaugeLink N} (a b : SU.E)
lemma one_off {i : gaugeLink N} (h:i≠e)(U:Pane N):oneOffer e a b U i=U i := by rw [oneOffer,switch,atom_off a h,atom_off b h,one_mul,mul_one]
lemma one_on (U:Pane N):oneOffer e a b U e=a * U e * b:=by simp only [oneOffer,switch,atomAt,Pi.mulSingle_eq_same]
lemma one_cost (U:Pane N)(i:gaugeLink N): Ch (G:=SU.group) (U i) (oneOffer e a b U i) ≤ ch a + ch b := by
  by_cases h:i=e
  · subst i; rw [one_on]; unfold Ch
    rw [show a* U e*b*(U e)⁻¹=a*(U e*b*(U e)⁻¹) by group]
    simpa only [SU.group.chord_conj] using SU.group.chord_triangle a (U e*b*(U e)⁻¹)
  rw [one_off _ _ h]; unfold Ch; rw [mul_inv_cancel,SU.group.chord_one]; exact add_nonneg (SU.group.chord_nonneg a) (SU.group.chord_nonneg b)
lemma plaquette_cost (p : Face (Per (More N))) (U:Pane N) :
    ch (Lattice.faceValue U p) ≤ ch (Lattice.faceValue (oneOffer e a b U) p)+4*(ch a+ch b) := by
  refine (ch_bound (G:=SU.group) _ (Lattice.faceValue (oneOffer e a b U) p)).trans (add_le_add_right ?_ _)
  exact (travel_ch (G:=SU.group) (fun i=>one_cost a b U i) _ (Lattice.square p.2.val.1 p.2.val.2)).trans_eq (by simp [Lattice.square])

lemma face_other (p : Face (Per (More N))) (U:Pane N)(h:e.1∉RG.touched p) :
    Lattice.faceValue (oneOffer e a b U) p = Lattice.faceValue U p := by
  apply WilsonStartup.face_local p
  exact fun i hi _=> one_off a b (fun k:i=e=> h (k ▸ hi)) _

/-- Require small plaquettes on the shifted config (χ test) -- do not assume
anything on plaquettes away from the shifted link. Strict flag rule unchanged. -/
lemma flags_stick {τ:ℝ}(v:0≤τ)(U:Pane N)(h:ch a+ch b≤τ/24)
    (lamp:∀ p:Face (Per (More N)), e.1∈RG.touched p → ch (Lattice.faceValue (oneOffer e a b U) p) < τ/3) :
    (∀ p :Face (Per (More N)),e.1∈RG.touched p→ ch (Lattice.faceValue U p)<τ/2) ∧
    (∀ p : Face (Per (More N)), ∀ {r:ℝ}, τ ≤ r →
      (ch (Lattice.faceValue (oneOffer e a b U) p) ≤ r ↔ ch (Lattice.faceValue U p) ≤ r)) := by
  have ht p he := (plaquette_cost (e:=e) a b p U).trans_lt (show ch (Lattice.faceValue (oneOffer e a b U) p) + 4 * (ch a + ch b) < τ/2 by linarith only [h,lamp p he])
  refine ⟨ht,fun p r x=>?_⟩
  by_cases z:e.1∈RG.touched p
  · refine iff_of_true ?_ ?_ <;> linarith only [ht p z,lamp p z,x,v]
  rw [face_other a b _ U z]

lemma flags_preserved {τ:ℝ}(v:0≤τ)(U:Pane N)(h:ch a+ch b≤τ/24)
    (lamp:∀ p:Face (Per (More N)), e.1∈RG.touched p → ch (Lattice.faceValue (oneOffer e a b U) p) < τ/3)
    {r:ℝ}(hr:τ≤r): flags r (oneOffer e a b U)=flags r U := by
  ext i; rw [RG.flags_spec,RG.flags_spec]
  exact exists_congr (fun p=>and_congr_right fun _=>lt_iff_lt_of_le_iff_le (flags_stick a b v U h lamp|>.2 p hr)) -- lemma?
lemma kept_stick {τ:ℝ}(v:0≤τ)(U:Pane N)(h:ch a+ch b≤τ/24)
    (lamp:∀ p:Face (Per (More N)), e.1∈RG.touched p → ch (Lattice.faceValue (oneOffer e a b U) p) < τ/3)
    (s:Signed)(x y:Skye.Seat N)(c:Clip) :
    RG.PathData.kept c τ y (Lattice.pull s x (oneOffer e a b U)) ↔ RG.PathData.kept c τ y (Lattice.pull s x U):= by
  unfold RG.PathData.kept
  apply forall_congr'; intro p
  have hz:0 ≤ (↑(separation y p.1):ℝ)/ c.relaxation := div_nonneg (by positivity) c.radius_pos.le
  rw [Face.send_price (oneOffer e a b U) p s x (Gauge.chord SU.group) SU.group.chord_inv (fun k g=>SU.group.chord_conj g k),
    Face.send_price U p s x (Gauge.chord SU.group) SU.group.chord_inv (fun k g=>SU.group.chord_conj g k)]
  exact (flags_stick a b v U h lamp).2 _ (le_mul_of_one_le_right v (Real.one_le_exp hz))
-- Define χ clearance region. s̄ rotor pressure puncture.
def clean (τ:ℝ)(q: Finset (Skye.Seat N))(U:Pane N):Prop:=
  ∀ (p:Face (Per (More N))) (x:Skye.Seat N), x∈q→x∈ RG.touched p → SU.group.chord (Lattice.faceValue U p)<τ

lemma clean_below {τ θ:ℝ} (U:Pane N){R:Finset (Skye.Seat N)} (h:ch a+ch b≤θ) (lamp:clean τ R (oneOffer e a b U)) : clean (τ+4*θ) R U := by
  intro p x hv t
  linarith only [plaquette_cost (e:=e) a b p U,lamp p x hv t,h]

lemma clean_disjoint_flags {τ θ:ℝ}(h:θ≤τ){U:Pane N}{R:Finset (Skye.Seat N)}(p:clean θ R U) :
    Disjoint (RG.flags τ U) R:= by
  refine Finset.disjoint_left.mpr ?_
  intro x w t
  obtain ⟨i,y,z⟩:= (RG.flags_spec ..).1 w
  exact z.not_ge ((p _ _ t y).le.trans h)

abbrev rotorWindow (r:ℕ)(e:gaugeLink N):= Lattice.halo (4*r+24) {e.1} -- large enough for far transmission proof
private lemma rotor_anchor (r:ℕ): e.1∈rotorWindow r e := by simp [rotorWindow,halo_spec]
private lemma ends_cost (i:gaugeLink N)(x:Skye.Seat N)(t:x ∈ Skye.ends i) : separation i.1 x ≤ 1 := by
  rcases Finset.mem_insert.mp ‹x ∈ _› with h|h
  · rw [h]; simp
  rw [Finset.mem_singleton.mp h]; exact Lat.oneTouch i.1 i.2
-- statement implicit binder x syntax?
private lemma win_clean {r:ℕ} (i:gaugeLink N)(h:separation e.1 i.1 ≤ 2*r+20):
    Skye.win r i ⊆ rotorWindow r e:= by
  intro x t; obtain ⟨z,p,v⟩:=Lattice.halo_spec.mp t
  apply Lattice.halo_spec.mpr
  refine ⟨e.1,Finset.mem_singleton_self _,?_⟩
  have hk:= separation_triangle i.1 z x; have hx:= ends_cost i z p; have hf:= separation_triangle e.1 i.1 x; omega

set_option maxHeartbeats 96000
/-- If the actually shifted U_z pays the patch tests, **same** Loom on the
old and shifted arg changes on precisely this link only. No tie, transmission
or extra Gauge assumption (Roof.lamp on all Ids; use #check to see if missing).
Guard threshold t in Roof ≥ physical τ (μ in G law). -/
theorem loom_oneOffer {τ t d:ℝ}{r:ℕ}{W:Scree.Loom N}(H:Roof N t d r W)(v:0≤τ)(g:τ≤ t)
    (U:Pane N)(k:Ids N)(h:ch a+ch b≤τ/24)(lamp:clean (τ/3) (rotorWindow r e) (oneOffer e a b U)):
    W (oneOffer e a b U,k) = oneOffer e a b (W (U,k)) := by
  let V := oneOffer e a b U
  let M:= RG.flags t U
  have hl p he := lamp p e.1 (rotor_anchor r) he
  have hw: RG.flags t V=M:= flags_preserved a b v U h hl g
  have hy:Disjoint M (rotorWindow r e):= clean_disjoint_flags (show τ/3+4*(τ/24) ≤ t by linarith) (clean_below a b U h lamp)
  have hY(i:gaugeLink N)(q:separation e.1 i.1 ≤ 2*r+20): Disjoint M (Skye.win r i):= Finset.disjoint_of_subset_right (win_clean i q) hy
  funext i; change W (V,k) i = _
  by_cases q:separation e.1 i.1 ≤2*r+20
  · rw [H.lamp V k i (hw.symm ▸ hY i q)]
    by_cases hi:i=e
    · subst i; change oneOffer e a b U e = oneOffer e a b (W (U,k)) e; rw [one_on,one_on,H.lamp U k e (hY e q)] -- proof V unfold
    rw [one_off _ _ hi,H.lamp U k i (hY i q)]; exact one_off _ _ hi U
  have hF:i≠e:=fun t=>q (by rw [t]; simp)
  rw [one_off _ _ hF]
  let X := ({e.1}:Finset (Skye.Seat N))ᶜ
  have hx: Skye.Week X (Skye.ends i) M r := by
    constructor
    · intro c hC y hY'
      obtain ⟨z,hz,kt⟩:= Lattice.halo_spec.mp hY'
      apply Finset.mem_compl.mpr
      intro hy
      rw [Finset.mem_singleton.mp hy] at kt
      apply q
      have hu:=ends_cost i z (hC hz); have hg:=separation_triangle i.1 z e.1; rw [separation_comm i.1 e.1] at hg; omega
    intro c _ j hj z ht
    obtain ⟨y,h,hr⟩:=Lattice.halo_spec.mp ht
    apply Finset.mem_compl.mpr; intro hv
    rw [Finset.mem_singleton.mp hv,Finset.mem_singleton.mp h] at hr
    exact Finset.disjoint_left.mp hy (Finset.mem_filter.mp hj).1 (Lattice.halo_spec.mpr ⟨e.1,Finset.mem_singleton_self _, by rw [separation_comm]; omega⟩)
  have ha:Agrees X V U:= fun f hv _=> one_off _ _ (fun l:f=e=> Finset.mem_compl.mp hv (by rw [l]; exact Finset.mem_singleton_self _)) U
  exact H.transmission V U k k X (Skye.ends i) (by rw [hw]) (hw.symm ▸ hx) hx ha (fun _ _=>rfl) i (by simp) (by simp)

-- Need pay face test including endpoints. Taking 4 extra halo layers suffices
def testRegion (x : Skye.Seat N) (δ : ℕ) := Lattice.halo (δ+4) {x}
lemma fits_face {x y : Skye.Seat N}{p:Face (Per (More N))}{δ:ℕ}(h:y∈Lattice.halo δ {x})(t:y∈RG.touched p): RG.touched p ⊆ testRegion x δ := by
  have he: separation x y ≤ δ:= by obtain ⟨a,r,e⟩:= Lattice.halo_spec.mp h; simpa only [Finset.mem_singleton.mp r] using e
  intro z q; refine Lattice.halo_spec.mpr ⟨x,Finset.mem_singleton_self _,?_⟩
  have hw:=separation_triangle x y z; have hb:=separation_triangle y p.1 z; rw [separation_comm y p.1] at hb; have ht:= Work.E01.sep_touched p y t; have hm:=Work.E01.sep_touched p z q; omega
lemma clean_local {x : Skye.Seat N}{δ:ℕ}{U V:Pane N}(h:Agrees (testRegion x δ) U V)(τ:ℝ) :
    clean τ (Lattice.halo δ {x}) U ↔ clean τ (Lattice.halo δ {x}) V:=by
  refine forall_congr' (fun p=> forall_congr' (fun y=> forall_congr' (fun hv=> forall_congr' fun hw=>?_)))
  rw [show faceValue U p=faceValue V p from WilsonStartup.face_local p U V (fun i e d=>h i (fits_face hv hw e) (fits_face hv hw d))]

lemma one_agrees {U V:Pane N}{S:Finset (Skye.Seat N)} (h:Agrees (↑S) U V):Agrees (↑S) (oneOffer e a b U) (oneOffer e a b V) := by
  intro i t v; by_cases hi : i=e
  · subst i; rw [one_on,one_on,h _ t v]
  rw [one_off _ _ hi _,one_off _ _ hi _,h _ t v]
end single

section many
variable {Q : Type*}(S:Q→Finset (Skye.Seat N))(E:Q → gaugeLink N)(a b:Q→SU.E)
    {τ t d:ℝ}{r:ℕ}{W:Scree.Loom N}(H:Roof N t d r W)(v:0≤τ)(g:τ≤t)
    (U:Pane N)(k:Ids N)(h:∀ q,SU.group.chord (a q)+SU.group.chord (b q)≤τ/24)
    (χ:Q→Finset (Skye.Seat N)) (lamp:∀ q,clean (τ/3) (χ q) (oneOffer (E q) (a q) (b q) U))
    (p:∀ j,(E j).1∈ S j) (m: Pairwise (Disjoint on S))
    (proper:∀ q,testRegion (E q).1 (4*r+24)⊆ S q) (tests:∀ q, rotorWindow r (E q) ⊆ χ q)
include p m in
lemma offerCons (qs : List Q){q:Q}(u:q ∉qs):
    offer (q::qs) E a b U = oneOffer (E q) (a q) (b q) (offer qs E a b U):=by
  funext i
  change ((atomAt _ _ i* offerSide qs E a i)*U i)*(atomAt (E q) (b q) i * offerSide qs E b i) = _
  by_cases hi:i=E q
  · subst i
    rw [offerSide_far qs E b (fun j hj=> anchor_avoid S m (fun v:j=q=>u (v ▸ hj)) (p q) (p j))]
    unfold oneOffer offer switch
    rw [offerSide_far qs E b (fun j hj=> anchor_avoid S m (fun v:j=q=>u (v ▸ hj)) (p q) (p j))]; group
  unfold oneOffer offer switch; rw [atom_off _ hi,atom_off _ hi]; group

include H v g h lamp proper tests p m in
/-- LP p.27 on all toggle subsets simultaneously even when oriented & using the
post-shift χ gate; disjointness required on the *measuring* regions including
all the shifted plaquettes, not disjointness of links alone.
This is at all U passing such χ including configs with arbitrary flag pattern elsewhere.
-/
theorem loom_toggles (qs:List Q)(n:qs.Nodup):
   W (offer qs E a b U,k) = offer qs E a b (W (U,k)) ∧
   (∀ {r':ℝ},τ ≤ r' → RG.flags r' (offer qs E a b U)=RG.flags r' U) ∧
   ∀ (s:Signed)(x y:Skye.Seat N)(c:Clip),
    RG.PathData.kept c τ y (Lattice.pull s x (offer qs E a b U)) ↔ RG.PathData.kept c τ y (Lattice.pull s x U) := by
  induction qs with
  | nil=> have he(V:Pane N):offer (Q:=Q) [] E a b V=V:=by funext i; change 1*V i*1=V i; simp
          rw [he,he]; exact ⟨rfl,fun _=>rfl,fun _ _ _ _=>Iff.rfl⟩
  | cons j qs ih=>
    obtain ⟨ha,hb⟩:=List.nodup_cons.mp n
    obtain ⟨hw,h',hw'⟩:=ih hb
    let V:=offer qs E a b U; let V' := oneOffer (E j) (a j) (b j) V
    have he:clean (τ/3) (rotorWindow r (E j)) V':= by
      have ht:= offer_undriven S qs E a b U p m (q:=j) ha
      have hf: Agrees (testRegion (E j).1 (4*r+24)) V' (oneOffer (E j) (a j) (b j) U) :=
        one_agrees _ _ (fun i hl hr=> ht i (proper j hl) (proper j hr))
      exact (clean_local hf _).2 (fun p x hp=> lamp j p x (tests _ hp))
    have ht(z)(v:(E j).1∈RG.touched z):=he z _ (rotor_anchor r) v
    rw [offerCons S E a b _ p m qs ha, offerCons S E a b _ p m qs ha]
    refine ⟨?_,?_,?_⟩
    · rw [loom_oneOffer (a j) (b j) H v g V k (h j) he, show W (V,k)=_ from hw]
    · intro r' t; rw [flags_preserved (a j) (b j) v V (h j) ht t]; exact h' t
    intro s x y c; rw [kept_stick (a j) (b j) v V (h j) ht s x y c]; apply hw'
end many

/- The physical shift amount |m|ε, ε=β'_s^(-9/16);
uniformly ≤ τ/(24C) eventually, for *all* admissible β'
(including any future path limit, no need to assume convergence on P.history now). -/
open Pressure
def rotorEps (β : ℝ) : ℝ:= ((Real.sqrt β)⁻¹)^(1+(1/8:ℝ))
private lemma eps_formula {β:ℝ}(h:0 ≤ β) : rotorEps β = β^(-(9/16:ℝ)) := by
  unfold rotorEps
  simp_rw [Real.sqrt_eq_rpow, ←Real.rpow_neg h, ←Real.rpow_mul h]; norm_num

lemma smallRotor : ∀ᶠ x:ℝ in atTop,0<x ∧ ∀ β:ℝ,x/2 ≤β → ∀ ξ:SU.group.Color, ‖ξ‖ ≤ 1 →
    ∀ w:ℝ,|w|≤24 → SU.group.chord (SU.group.lieExp ((w*rotorEps β) • ξ)) ≤ Pressure.temp x/24 := by
  obtain ⟨C,δ,hC,hδ,hp⟩:= Next.Fluctuations.chord_chart_cost SU.group
  let E(x:ℝ):=x^(-(1/2:ℝ)); let B(x:ℝ):= x^(-(1/16:ℝ)); let D:ℝ:= 2^(9/16:ℝ)
  have hB:Tendsto B atTop (𝓝 0):=tendsto_rpow_neg_atTop (by norm_num)
  have hd:0<D:=by unfold D; positivity
  have hl:Tendsto (fun x=>24*D*B x) atTop (𝓝 0):=by simpa using hB.const_mul (24*D)
  filter_upwards [eventually_ge_atTop (1:ℝ),hl.eventually (gt_mem_nhds hδ),hl.eventually (gt_mem_nhds (show 0<1/(24*C) by positivity))] with x he ht hr
  have hx:=zero_lt_one.trans_le he; have hE:0<E x:= Real.rpow_pos_of_pos hx _
  have hu:E x ≤ 1:= Real.rpow_le_one_of_one_le_of_nonpos he (by norm_num)
  have htE:E x ≤ Pressure.temp x:=by
    unfold E Pressure.temp; rw [Real.sqrt_eq_rpow, ←Real.rpow_neg hx.le]
    exact le_mul_of_one_le_right hE.le (Real.one_le_exp (sq_nonneg _))
  refine ⟨hx,fun β hw ξ hξ w hv=>?_⟩; have hβ:0<β:= (half_pos hx).trans_le hw
  have hz: rotorEps β ≤ D*(B x * E x):=by
    rw [eps_formula hβ.le]; refine (Real.rpow_le_rpow_of_nonpos (half_pos hx) hw (by norm_num)).trans ?_
    have hh:x^(-(9/16:ℝ))=B x*E x:=by unfold B E; rw [←Real.rpow_add hx]; congr 1; ring
    rw [Real.div_rpow hx.le (by norm_num), Real.rpow_neg (show 0 ≤ (2:ℝ) by norm_num),div_inv_eq_mul, mul_comm, hh]
  have hf:0≤rotorEps β:=by rw [eps_formula hβ.le]; exact Real.rpow_nonneg hβ.le _
  let z:=(w*rotorEps β) • ξ
  have ha:‖z‖ ≤ (24*D*B x)* E x:= by
    unfold z
    rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hf]
    grw [hv,hξ,hz]; apply le_of_eq; ring
  have hg:0 ≤ 24*D*B x :=by unfold B; positivity
  change SU.group.chord (SU.group.lieExp z) ≤ _
  refine (hp z (ha.trans ((mul_le_of_le_one_right hg hu).trans ht.le))).trans ((mul_le_mul_of_nonneg_left ha hC.le).trans ?_)
  have hi: C*(24*D*B x)≤1/24:=by
    apply (le_div_iff₀ (by norm_num:(0:ℝ)<24)).mpr
    nlinarith only [(le_div_iff₀ (by positivity)).mp hr.le]
  linarith only [mul_le_mul_of_nonneg_right hi hE.le,htE]


-- Parameters for orientations. pos e shift by exp(Mε ξ), on moved negative
-- edge perform the *left* shift on oriented link Ue⁻¹ (right multiply its
-- stored positive value by inverse). Conjugate shifts on parallel transports
-- can then just use right normalized group decisions, no compatibility assumed
-- with detector phase.
def rotorElem (w β :ℝ)(ξ:SU.group.Color):SU.E:= SU.group.lieExp ((w*rotorEps β) • ξ)
def rotorLeft (neg:Bool)(w β:ℝ)(ξ:SU.group.Color):SU.E:= if neg then 1 else rotorElem w β ξ
def rotorRight (neg:Bool)(w β:ℝ)(ξ:SU.group.Color):SU.E:= if neg then (rotorElem w β ξ)⁻¹ else 1

variable (P: Spine)
local notation "Λ" => P.par
local notation "Y" => P.run
local notation "X(" s ")" => hat P.par.R.L P.par.x s
set_option quotPrecheck false
local notation "τ(" s ")" => ((Y).meter.a s).threshold
local notation "n(" s "," i ")" => side P.run i s
local notation "T" => P.par.J.k
local notation "d0" => P.par.d
local notation "r0" => P.par.J.n
private lemma rotor_spectrum : ∀ᶠ s:ℕ in atTop,∀ β ξ w neg, X(s)/2 ≤ β → ‖ξ‖ ≤1 → |w| ≤24 →
  SU.group.chord (rotorLeft neg w β ξ) + SU.group.chord (rotorRight neg w β ξ) ≤ τ(s)/24 := by
  filter_upwards [(turnover (Λ)).eventually smallRotor] with s v β ξ w neg h he hw
  have ht:= v.2 β h ξ he w hw
  rw [show τ(s)=Pressure.temp X(s) from ((Y).meter.boot s).1]
  cases neg <;> simpa [rotorLeft,rotorRight,rotorElem] using ht

universe u
/-- G, F, LZ, LP toggled mask + Loom receipt at the incurred strength;
every ticker P and on the exact S-system of P.run (the **quantity
K** with these angular data isn't separately funded by this lemma; this is
for the LZ kernel/warm exponent applicability to such transactions and the
Ward identity calculation in LP). Keep geometry qualifications precisely;
e.g. χ is the ball on which chord < τ/3 on all touching faces. Never assume
agreements under shifts at ε for every configuration without that χ.
-/
theorem physical_toggles : ∀ᶠ s:ℕ in atTop,∀ i:ℕ,∀ β:ℝ,X(s)/2 ≤β→
    let n:=Papal.count (Y) s i;
    let W:=Papal.room (Y) s i;
    ∀ (Q:Type u)(S:Q→Finset (Skye.Seat n))(E:Q → gaugeLink n)
      (w:Q→ℝ)(xi:Q→SU.group.Color)(neg:Q→Bool),
      (∀ q,|w q|≤24) → (∀ q,‖xi q‖≤1) → (∀ q,testRegion (E q).1 (4*r0+24) ⊆ S q) → Pairwise (Disjoint on S) →
      let a:=fun q=> rotorLeft (neg q) (w q) β (xi q); let b:=fun q=> rotorRight (neg q) (w q) β (xi q);
      ∀ (U:Pane n)(j:Ids n),
      (∀ q,clean (τ(s)/3) (rotorWindow r0 (E q)) (oneOffer (E q) (a q) (b q) U)) →
      ∀ (l:List Q),l.Nodup→let V:=offer l E a b U
        W (V,j)= offer l E a b (W (U,j)) ∧ RG.flags τ(s) V = RG.flags τ(s) U ∧ RG.flags T V = RG.flags T U ∧
        ∀ (z:Signed)(y:Skye.Seat n), RG.PathData.kept (Λ).K.top.clip τ(s) y (Lattice.pull z 0 V) ↔
          RG.PathData.kept (Λ).K.top.clip τ(s) y (Lattice.pull z 0 U):= by
  filter_upwards [rotor_spectrum P] with s c i β hu n W Q S E w xi neg hw hm hR hM a b U j hU l hn V
  have hJ(q): (E q).1∈ S q:=hR q (by simp [testRegion,halo_spec])
  have hτ:= (P.run.paidM.pole s)
  obtain ⟨A,X,F⟩:=loom_toggles S E a b (Papal.roofage (Y) i s) ((P.run.meter.a s).threshold_pos.le) hτ U j
    (fun q=> c β _ _ _ hu (hm q) (hw q)) _ hU hJ hM hR (fun _=>Finset.Subset.refl _) l hn
  exact ⟨A,X le_rfl,X hτ,fun z y=> F z 0 y _⟩
end PureForce
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
