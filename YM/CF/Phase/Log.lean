import YM.CF.Phase.Bridges

/-! Exact complex-log relative transport. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Phase
open Cube Lat Lattice SU Fock Finset Filter
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {m B : Side}

def logs (m B : Side) (c : Part m B) (U : Skin m B) (x y : Cue m) :=
    @dite _ (∃ a, Arch m B U x y a) (Classical.propDecidable _) (fun h=>bill m B c U x y h.choose) fun _=> (0:ℂ)
lemma slot_cont (m : Side) : Continuous (slot m) := continuous_pi (fun i=>continuous_apply _)
lemma twin_cont (m : Side) : Continuous (fun t : Cue m × Cue m=>twin m t.1 t.2) := by
  refine continuous_pi fun i=>?_; simp only [twin,capRow,slot]; split <;> fun_prop
lemma open0 (m B : Side) : IsOpen {t : Skin m B×Cue m|ZeroF m B t.1 t.2} := by
  let f := fun t:Skin m B×Cue m=>(t.1,slot m t.2)
  exact (open_verified m B {0}).preimage (show Continuous f from continuous_fst.prodMk ((slot_cont m).comp continuous_snd))
lemma openB (m B : Side) : IsOpen {t : Skin m B×Cue m×Cue m|EdgeP m B t.1 t.2.1 t.2.2} := by
  let f := fun t:Skin m B×Cue m×Cue m=>(t.1,twin m t.2.1 t.2.2)
  exact (open_verified m B _).preimage (show Continuous f from continuous_fst.prodMk ((twin_cont m).comp continuous_snd))
section
variable (c : Part m B) {e : ℝ} (b : Room B e) {U : Skin m B} (g : Guard U e)
include b g
lemma echoes (x y : Cue m) (z : Cue m) (h : Arch m B U x y z) : logs m B c U x y=bill m B c U x y z := by
  classical
  let f : ∃ z, Arch m B U x y z := ⟨_,h⟩; unfold logs; rw [dif_pos f]; exact voice c b g x y _ _ f.choose_spec h
lemma allotted {x y w} (h : ZeroF m B U x) (k : ZeroF m B U y) (u : ZeroF m B U w) :
    logs m B c U x y+logs m B c U y w=logs m B c U x w := by
  classical
  have H : ({x,y,w}:Finset (Cue m)).card≤6 := (card_insert_le ..).trans ((Nat.add_le_add_right (card_insert_le y {w}) 1).trans (by simp))
  obtain ⟨z,v⟩ := ties (U:=U) H id (by simp [h,k,u]); simp only [forall_mem_insert,mem_singleton,forall_eq,id_eq] at v
  rw [echoes c b g _ _ _ ⟨v.1,v.2.1⟩,echoes c b g _ _ _ ⟨v.2.1,v.2.2⟩,echoes c b g _ _ _ ⟨v.1,v.2.2⟩]
  unfold bill; abel
lemma bill_fill (x y : Cue m) (E : EdgeP m B U x y) :
    Complex.exp (amount m B c U x y) • filled (lens m B c U) (pair m B U x)=filled (lens m B c U) (pair m B U y) := by
  have he := ray_filled c b g (show Verified _ _ _ _ _ _ from E) (stick_in 0 (show (0:Row)∈insert 1 {0} by simp)) (stick_in 1 (show (1:Row)∈insert 1 {0} by simp)) -- unfolds?
  rw [spot_pair 0 (x:=x) _ (fun j=>by simp [twin,capRow,slot]),spot_pair 1 (x:=y) _ (fun j=>by simp [twin,capRow,slot])] at he
  exact he
lemma log_fill (x y : Cue m) (h : ZeroF m B U x) (k : ZeroF m B U y) :
    Complex.exp (logs m B c U x y) • filled (lens m B c U) (pair m B U x)=filled (lens m B c U) (pair m B U y) := by
  obtain ⟨z,G,H⟩ := arches h k
  rw [echoes c b g x y z ⟨G,H⟩,bill, Complex.exp_sub,div_eq_inv_mul, mul_smul,bill_fill c b g x z G, ← bill_fill c b g y z H, smul_smul,inv_mul_cancel₀ (Complex.exp_ne_zero _),one_smul]
end
abbrev partner (m B : Side) (k : Site (Domain m B)→E) (x : Cue m) : Cue m := fun i=>scaledV (k (address m B i)) (x i)
lemma twist_0 {m B : Side} (U : Skin m B) (x) (g : Site (Domain m B)→E) : ZeroF m B (gauge g U) (partner m B g x) ↔ ZeroF m B U x := verified_g U g margin (slot m x) {0}
lemma twin_g (x y : Cue m) (k : Site (Domain m B)→E) : twin m (partner m B k x) (partner m B k y)=onF k (twin m x y) := by
  funext i; unfold twin partner onF capRow slot; split <;> simp_all
lemma twist_e (U : Skin m B) (x y) (g : Site (Domain m B)→E) : EdgeP m B (gauge g U) (partner m B g x) (partner m B g y) ↔ EdgeP m B U x y := by rw [EdgeP,EdgeP,twin_g,verified_g]
lemma pair_g (U : Skin m B) (x) (g : Site (Domain m B)→E) : pair m B (gauge g U) (partner m B g x)=congrC (conjG matter (g ∘ node)) (pair m B U x) := bow_g (U:=U) (s:=slot m x) (q:=stick 0) g
variable (c : Part m B) {e : ℝ} (b : Room B e) {U : Skin m B}
include b
lemma gain_g (x y : Cue m) (k : Site (Domain m B)→E) (g : Guard U e) (h : EdgeP m B U x y) :
    amount m B c (gauge k U) (partner m B k x) (partner m B k y)=amount m B c U x y := by
  rw [amount,twin_g]
  exact ray_g c b g (show Verified _ _ _ _ _ _ from h) (stick_in 0 (show (0:Row)∈insert 1 {0} by simp)) (stick_in 1 (show (1:Row)∈insert 1 {0} by simp)) k
lemma transport_log (x y : Cue m) (k : Site (Domain m B)→E) (g : Guard U e) (h : ZeroF m B U x) (l : ZeroF m B U y) :
    logs m B c (gauge k U) (partner m B k x) (partner m B k y)= logs m B c U x y := by
  obtain ⟨z,H⟩ := arches h l
  have hG := (twist_e U x z k).mpr H.1; have hT := (twist_e U y z k).mpr H.2
  rw [echoes c b (Guard.cov g k) _ _ (partner m B k z) ⟨hG,hT⟩, echoes c b g _ _ z H,bill,bill,gain_g c b x _ _ g H.1,gain_g c b y _ _ g H.2]
def Ear (m B : Side) (e : ℝ) := {t : Skin m B × Cue m × Cue m|Guard t.1 e ∧ EdgeP m B t.1 t.2.1 t.2.2}
def Rim (m B : Side) (e : ℝ) := {t : Skin m B × Cue m × Cue m|Guard t.1 e ∧ ZeroF m B t.1 t.2.1 ∧ ZeroF m B t.1 t.2.2}
lemma amt_cont : ContinuousOn (fun t : Skin m B× Cue m × Cue m => amount m B c t.1 t.2.1 t.2.2) (Ear m B e) := by
  let F := fun t:Skin m B × Cue m× Cue m=>((t.1,twin m t.2.1 t.2.2),stick 0,stick 1)
  have H : Continuous F := (continuous_fst.prodMk ((twin_cont m).comp continuous_snd)).prodMk continuous_const
  let r : Zone := insert (1:Row) {0}
  let R := fun t : AxisY m B => ray m B c t.1.1 t.1.2 t.2.1 t.2.2
  change ContinuousOn (R ∘ F) _
  apply ContinuousOn.comp (rays_cont c b (r:=r)) H.continuousOn
  intro t ht; exact ⟨⟨ht.1,ht.2⟩, stick_in 0 (show (0:Row)∈r by simp [r]), stick_in 1 (show (1:Row)∈r by simp [r])⟩
omit b in
lemma localsC {X : Type*} [TopologicalSpace X] (f t : X → ℂ) (F G : X→X) (A J : Set X) (x : X) (hf : ContinuousOn f A) (h₁ : Continuous F) (h₂ : Continuous G) (he : F x∈A) (hu : G x∈A) (H : x∈J)
    (hs : ∀ᶠ u in nhdsWithin x J, F u∈A) (ht : ∀ᶠ u in nhdsWithin x J, G u∈A) (hg : ∀ u∈J, F u∈A → G u∈A → t u=f (F u)-f (G u)) :
    ContinuousWithinAt t J x := by
  let v := (f ∘ F)-(f ∘ G)
  have hF : ContinuousWithinAt (f ∘ F) J x := Tendsto.comp (hf _ he) (tendsto_nhdsWithin_iff.mpr ⟨h₁.continuousAt.continuousWithinAt,hs⟩)
  have hG : ContinuousWithinAt (f ∘ G) J x := Tendsto.comp (hf _ hu) (tendsto_nhdsWithin_iff.mpr ⟨h₂.continuousAt.continuousWithinAt,ht⟩)
  change Tendsto _ _ (𝓝 (t x)); rw [show t x=v x from hg _ H he hu]
  apply Tendsto.congr' _ (show ContinuousWithinAt v J x from hF.sub hG)
  filter_upwards [self_mem_nhdsWithin, hs, ht] with u hx hu hv; exact (hg _ hx hu hv).symm
omit b in
lemma open_switch {X : Type*} [TopologicalSpace X] (F:X→X) (A D : Set X) (x : X) (h : Continuous F) (e : IsOpen D) (g : F x ∈ D) : ∀ᶠ y in nhdsWithin x A, F y ∈ D := h.continuousAt.continuousWithinAt (e.mem_nhds g)
lemma etude : ContinuousOn (fun t : Skin m B× Cue m × Cue m => logs m B c t.1 t.2.1 t.2.2) (Rim m B e) := by
  rintro ⟨U,x,y⟩ ⟨h,g,k⟩
  obtain ⟨z,H,K⟩ := arches g k
  let F := fun t: Skin m B × Cue m × Cue m=>(t.1,t.2.1,z)
  let G := fun t: Skin m B × Cue m × Cue m=>(t.1,t.2.2,z)
  have hf : Continuous F := continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk continuous_const)
  have hg : Continuous G := continuous_fst.prodMk ((continuous_snd.comp continuous_snd).prodMk continuous_const)
  let f := fun t: Skin m B× Cue m × Cue m => amount m B c t.1 t.2.1 t.2.2
  let J := Rim m B e
  let t := (U,x,y)
  have h₁ : ∀ᶠ u in nhdsWithin t J, EdgeP m B u.1 u.2.1 z := open_switch F J _ _ hf (openB m B) (show EdgeP m B _ _ _ from H)
  have h₂ : ∀ᶠ u in nhdsWithin t J, EdgeP m B u.1 u.2.2 z := open_switch G J _ _ hg (openB m B) (show G t∈ _ from K)
  have hw : ∀ᶠ u in nhdsWithin t J, Guard u.1 e := by filter_upwards [self_mem_nhdsWithin] with u hx; exact hx.1
  let A := Ear m B e
  let L := fun t : Skin m B×Cue m×Cue m => logs m B c t.1 t.2.1 t.2.2
  change ContinuousWithinAt L J t
  have W (u) (h : u∈J) (hu : F u ∈ A) (hv : G u∈ A) : L u=f (F u)-f (G u) := echoes c b h.1 u.2.1 u.2.2 z ⟨hu.2,hv.2⟩
  exact localsC f L F G A J t (amt_cont c b) hf hg ⟨h,H⟩ ⟨h,K⟩ ⟨h,g,k⟩ (hw.and h₁) (hw.and h₂) W
end YM.CF.Phase
