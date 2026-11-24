import YM.CF.Mir.Spin

/-! Exact symmetry of the global logarithm. Thus any local allocation can be mirrored. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mir.Trip
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset
attribute [local instance] opCStarAlgebra
variable {N m B : Side}
lemma dominated {e} (a : Trip m) (t) (g:t∈payer m B e) : onPack B a t∈payer m B e := ⟨through_guard a g.1,(term_turn ..).mpr g.2⟩
lemma flip_bill (a : Trip m) {e : ℝ} {U : Skin m B} {x : Cue m} (c d : Phase.Part m B) (b : Room B e) (g : Guard U e) (k : ZeroF m B U x) (h : ∀ (s : ArrayF m) (r : Zone), Verified m B margin U s r → ∀ i∈zone r,∀ j∈zone r,
    ray m B d (through B a U) (riseF a s) i j=a.flips (ray m B c U s i j)) : accord m B d (through B a U) (a.oncue x)=a.flips (accord m B c U x) := by
  have ht y (e:ZeroF m B U y) : logs m B d (through B a U) (oncue a y) (oncue a x)=a.flips (logs m B c U y x) := by
    obtain ⟨q,w,L⟩ := arches e k
    have he z (h : EdgeP m B U z q) : EdgeP m B (through B a U) (oncue a z) (oncue a q) := by rw [EdgeP, a.twin_turn]; exact (verified_turn a _ U _).mpr h
    rw [echoes _ b (through_guard a g) _ _ (a.oncue q) ⟨he y w,he x L⟩, echoes c b g _ _ q ⟨w,L⟩, bill,bill,flips_sub]
    have H x (g:EdgeP m B U x q) : amount m B d (through B a U) (oncue a x) (oncue a q)=a.flips (amount m B c U x q) := by rw [amount,twin_turn]; exact h _ Knot g _ (stick_in _ (by simp [Knot])) _ (stick_in _ (by simp [Knot]))
    rw [H _ w, H _ L]
  unfold accord; rw [←rains_rev a]
  let f := fun y=>lyre m B c U x y
  have he (y) : lyre m B d (through B a U) (oncue a x) (oncue a y)= a.flips (lyre m B c U x y) := by
    unfold lyre; rw [law_turn]; by_cases h : law m B U y=0
    · rw [h]; unfold flips; split <;> simp
    rw [ht y (law_rich m B _ _ h)]; unfold flips; split <;> simp
  simp_rw [he]; unfold flips; split <;> first | rfl | rename_i e
  simp only [Complex.star_def]; exact integral_conj -- tune
def Settled (m B : Side) (e : ℝ) (a : Trip m) := ∀ (t:Pack m B) (c:Phase.Part m B),t∈payer m B e→Phase.fund m B c (through B a t.1) (a.oncue t.2)= a.flips (Phase.fund m B c t.1 t.2)
lemma paid_step (a : Trip m) {e : ℝ} (p : Room B e) (i : Axis) (K : ∀ j, a.glare j=true ↔ j=i) : Settled m B e a := by
  rintro ⟨U,x⟩ c h; let V := a.pinTrip i B; let d := far B a c; let Z := through B a U
  have hu : Guard U e := h.1; have hx : ZeroF m B U x := h.2
  have he : Guard Z e := through_guard a hu; have ht := (term_turn a U x).mpr hx
  have hz : lens m B d Z=twist V (1-lens m B c U) := by
    have H := projector_twist (wiel_ok c p hu) V; rw [seaH a i K U c, minusP (wiel_ok d p he)] at H -- order tune
    change twist V (lens m B c U)= 1-lens m B d Z at H; rw [map_sub,map_one,H,sub_sub_cancel]
  have hV : ∀ x, a.flips x=star x := by
    intro v; rw [flips,show univ.filter (fun j=> a.glare j=true)= {i} by ext; simp [K], if_pos (by simp)]
  have hb := flip_bill a c d p hu hx (fun s r h i' hi j hj => by
    rw [hV];
    have hh : ∀ t∈zone r,(bow m B U s i').det = (bow m B U s t).det := fun t v=> field_det_match (grain_unit p hu h hi) (grain_unit p hu h v)
    exact swung c d p hu he hi hj V h ((verified_turn ..).mpr h) hz (fun x _=>shade_pin ..) hh)
  have H : pair m B Z (a.oncue x)=congrC V (pair m B U x) := shade_pin a U (slot m x) _ _
  have hp : netsal (lens m B d Z) (pair m B Z (oncue a x))=netsal (lens m B c U) (pair m B U x) := by
    apply Real.exp_injective; rw [salary d p he ht,salary c p hu hx,H,hz, filled_twist, act_unit_norm]; obtain ⟨n,l,-⟩ := kappa c p hu hx; exact compFilled (lensP _ p hu) (⟨_,n⟩:UNI (Model _)) l
  dsimp only at * -- tune
  change Phase.fund m B c Z _=_; rw [funding c d p he ht]; change Phase.fund m B d (through B a U) (a.oncue x)=a.flips (Phase.fund m B c U x)
  unfold Phase.fund; rw [hp,hb,hV,hV]; simp
lemma paid_plain (a : Trip m) {e : ℝ} (p : Room B e) (K : ∀ j, a.glare j=false) : Settled m B e a := by
  rintro ⟨U,x⟩ c h; let V := siteM (fperm m B a); let d := far B a c; let Z := through B a U
  have hu : Guard U e := h.1; have hx : ZeroF m B U x := h.2
  have he : Guard Z e := through_guard a hu; have ht := (term_turn a U x).mpr hx
  have hz : lens m B d Z=twist V (lens m B c U) := by
    have H := projector_twist (wiel_ok c p hu) V; rw [show twist V _=_ from careH a K U c] at H -- tune
    exact H.symm
  have hV : ∀ x, a.flips x=x := by intro v; simp [flips,K]
  have hk (s t) : bow m B Z (a.riseF s) t=congrC V (bow m B U s t) := by unfold Z; rw [bow,played, ←siteField]; rfl
  have hb := flip_bill a c d p hu hx (fun s r h i hi j hj=>by
    rw [hV]; unfold ray; apply sum_congr rfl; intro l hl; have hv := mem_range.mp hl
    have hm := inc_in hi hj B hv.le; have hM := inc_in hi hj B hv
    change rad _ _ _ Z _ _ _ _= _; unfold rad; rw [hz,hk,hk]; exact spark_turn (bow_ok c p hu h hm).2 (short c p hu h hm hM (inc_gap hi hj B l)) V)
  have H : pair m B Z (a.oncue x)=congrC V (pair m B U x) := hk (slot m x) (stick 0)
  have hp : netsal (lens m B d Z) (pair m B Z (oncue a x))=netsal (lens m B c U) (pair m B U x) := by apply Real.exp_injective; rw [salary d p he ht, salary c p hu hx, H,hz,filled_twist,act_unit_norm]
  change Phase.fund m B c Z _=_; rw [funding c d p he ht]; change Phase.fund m B d (through B a U) _=_
  rw [hV]; change Phase.fund m B d Z _=Phase.fund m B c U _; unfold Phase.fund; rw [hp,show accord m B d Z _=_ from hb,hV]
lemma settled_op {a b : Trip m} {e : ℝ} (h : Settled m B e a) (k : Settled m B e b) : Settled m B e (a*b) := fun t c g=> calc
  _ = b.flips (Phase.fund m B c (through B a t.1) (oncue a t.2)) := by rw [←through_comp, ←cue_comp]; exact k (onPack B a t) c (dominated a t g)
  _ = _ := by rw [h t c g,flips_comp]
theorem settledAll (a : Trip m) {e : ℝ} (b:Room B e) : Settled m B e a := by
  let Z (S : Finset Axis) (v : Site (More m)) : Trip m := ⟨fun i=>decide (i∈S),v⟩
  have hz (T) : ∀ v:Site (More m), Settled m B e (Z T v) := by -- tune
    induction T using Finset.induction_on with
    | empty => exact fun _=> paid_plain _ b (fun i=> by simp [Z])
    | @insert i s g ih =>
      intro v; let A := Z {i} 0
      rw [show Z (insert i s) v= Z s v*A by
        apply Trip.ext; funext j; by_cases k:j=i
        · subst j; simp [A,Z,glarex,g]
        simp [A,Z,glarex,k]
        rw [movep,show A.move=0 from rfl,Signed.act_zero, zero_add]]
      exact settled_op (ih v) (paid_step A b i (fun j=>by simp [A,Z]))
  rw [show a=Z (univ.filter (a.glare ·=true)) a.move by apply Trip.ext; funext i; cases e:a.glare i <;> simp [Z,e]; rfl]; exact hz _ _
end YM.CF.Mir.Trip
