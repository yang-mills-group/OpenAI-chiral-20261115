import GaugeFieldConstruction.Wide

/-!
# Continuous proper rotations. Infinitesimal prices in the actual programs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Stage.Wide
open Cauchy Row Phys Function Finset Submodule U1 Flux One
open Matter (Slot)
open scoped BigOperators
open Cell

def Theta := wings UnitV UnitV
def PG := Theta.wings Theta
def PG1:= Theta.wings (Theta.wings UnitV)
def PT1 := UnitV.wings (UnitV.sum UnitV)
def PT2:= UnitV.wings (Theta.sum (Theta.sum Theta))
def PX (r c : Bool): Cell MX := Cell.wings (if c then UnitV else Still Axis) (if r then Theta else Still W)
section convergence
-- for `Match` and `Fast` availability
lemma fθ : Fast leaves Theta:= fast_cross brisk brisk
lemma fG1 : Fast leaf4 PG:= fast_cross fθ fθ
lemma fG2 : Fast leaf5 PG1:= fast_cross fθ (fast_cross fθ brisk)
lemma fP : Fast Raw.f3Act UnitV := fast_twist brisk
lemma fQ : Fast Raw.f4Act PT1:= fast_cross fP (fast_sum fP brisk)
lemma fR : Fast stem5 PT2:= fast_cross fP (fast_sum (fast_cross fP fP) (fast_sum fθ (fast_cross brisk fP)))
variable {α : Type*} [Fintype α] [DecidableEq α]
lemma vacant (Ω i) : beta (Still α) Ω i=0 := by
  have H : beta (Still α) Ω=0 := ket_ext fun i=>by simp [Cell.beta,Still,bill]
  rw [H]; rfl
lemma vacs (A : Labels α) : Fast A (Still α):= by intro s B i; rw [vacant,vacant,map_zero]
lemma fX (r c): Fast horse (PX r c):= by
  cases r <;> cases c
  · exact fast_cross (vacs Raw.v) (vacs leaves)
  · exact fast_cross brisk (vacs leaves)
  · exact fast_cross (vacs Raw.v) fθ
  exact fast_cross brisk fθ
lemma mθ : Match leaves Theta:= match_cross merit merit
lemma mG1 : Match leaf4 PG:= match_cross mθ mθ
lemma mG2 : Match leaf5 PG1:= match_cross mθ (match_cross mθ merit)
lemma mP : Match Raw.f3Act UnitV:= match_twist merit
lemma mQ : Match Raw.f4Act PT1:= match_cross mP (match_sum mP merit)
lemma mR : Match stem5 PT2:= match_cross mP (match_sum (match_cross mP mP) (match_sum mθ (match_cross merit mP)))
lemma mX : Match horse (PX true true):= match_cross merit mθ
end convergence

variable {K : Dollars} (h : Course K) {Ω : Rotors} (p : Toll K Ω.val) (m : ℂ) (V : Bool→ℂ)
variable {s : Pig}
-- Linear evaluation of labels

lemma sheet_step (i : W) (Ω):jet sheet (Theta.beta Ω (ket i))= Wd Ω.val i.1 i.2 := by
  rw [← takes i.1 i.2,Theta,optionB,split_legs,betaV,betaV]
  simp_rw [map_add, Wd,map_sum, map_smul,LinearMap.sum_apply, LinearMap.smul_apply,takes,on_ket]; rw [Finset.sum_add_distrib]; simp_rw [map_sum,map_smul,on_ket]; rfl

include h p
lemma leaf_touch (i : W) (s:Pig): (Flash (gStress m)).Touch K m (atop s (sheet i)) (atop s (jet sheet (Theta.beta Ω (ket i)))) := by rw [sheet_step]; exact lampG h p m s _ _

def leafD (t : W × Axis):= Gder t.2 (sheet t.1)
lemma leaf_D (i : W×Axis) (s:Pig): (Flash (gStress m)).Touch K m (atop s (leafD i)) (atop s (jet leafD ((Theta.wings UnitV).beta Ω (ket i)))) := by
  have H : jet leafD (times' (Theta.beta Ω (ket i.1)) (ket i.2))=Gder i.2 (jet sheet (Theta.beta Ω (ket i.1))) := by
    have he : jet leafD ∘ₗ times'.flip (ket i.2) = Gder i.2 ∘ₗ jet sheet := ket_ext (fun j=>by simp [leafD,LinearMap.flip_apply])
    exact LinearMap.congr_fun he _
  rw [← takes i.1 i.2,optionB,split_legs, map_add,H,betaV]; simp_rw [map_sum,map_smul,map_add,takes,on_ket, leafD, here (Gder _)]
  simp_rw [map_sum,map_smul,here (Gder _) s]
  exact (Flash (gStress m)).expand h p (leaf_touch h p m i.1 s) i.2

omit h p in
lemma play {α β : Type*} (f : α→GJet) (g : β→ GJet) (x : J α) (y : J β): jet (fun v:α×β=> Bose (f v.1) (g v.2)) (times' x y)=Bose (jet f x) (jet g y):=by
  let D : GJet →ₗ[ℂ] GJet→ₗ[ℂ] J Row.g:= times'+times'.flip
  have h : times'.compr₂ (jet (fun v:α×β=> Bose (f v.1) (g v.2)))= D.compl₁₂ (jet f) (jet g) := equalsB (fun i j=>by change jet _ (times' _ _) = _; rw [takes,on_ket]; simp [D,Bose])
  exact LinearMap.congr_fun (LinearMap.congr_fun h x) y

omit p in
lemma links {x y U T : GJet} (p : ∀ (s : Pig),(Flash (gStress m)).Touch K m (atop s x) (atop s U)) (q : ∀ (s : Pig),(Flash (gStress m)).Touch K m (atop s y) (atop s T)) :
    (Lamp.gloG (gStress m)).Touch K m (graph_g (Bose x y)) (graph_g (Bose U y+Bose x T)) := by
  let L:=Flash (gStress m); let M:=Lamp.gloG (gStress m)
  have he s: M.Touch K m (yD s s (Bose x y)) (yD s s (Bose U y+Bose x T)) := by
    have H := M.plus h (Lamp.to_touch (L.merger L h (p s) (q s)) _) (Lamp.to_touch (L.merger L h (q s) (p s)) _) -- adjust
    simp only [Bose,yD,map_add,straps]
    rw [show times' (atop s U) (atop s y) + times' (atop s y) (atop s U) + (times' (atop s x) (atop s T)+times' (atop s T) (atop s x))= times' (atop s U) (atop s y)+times' (atop s x) (atop s T)+(times' (atop s T) (atop s x)+times' (atop s y) (atop s U)) by abel]; exact H
  rw [graph_g,LinearMap.smul_apply,LinearMap.smul_apply, LinearMap.sum_apply,LinearMap.sum_apply]; exact M.wish (Lamp.sums_T h _ _ _ (fun i _=>he i)) _
lemma crown (i : GE):(Lamp.gloG (gStress m)).Touch K m (graph_g (page i)) (graph_g (jet page (PG.beta Ω (ket i)))) := by
  rw [PG,optionB,← takes i.1 i.2, split_legs,map_add (jet _)]
  simp_rw [show page=(fun p=>Bose (sheet p.1) (sheet p.2)) from rfl,play,on_ket]
  exact links h m (leaf_touch h p m i.1) (leaf_touch h p m i.2)
lemma crossV (i : G1):(Lamp.gloG (gStress m)).Touch K m (graph_g (pageV i)) (graph_g (jet pageV (PG1.beta Ω (ket i)))) := by
  rw [PG1,optionB,← takes i.1 i.2,split_legs,map_add (jet _)]
  simp_rw [show pageV=(fun p=>Bose (sheet p.1) (leafD p.2)) from rfl,play,on_ket]
  exact links h m (leaf_touch h p m i.1) (leaf_D h p m i.2)

-- PH labels are prepared together with their spin rotations
omit h p
variable {c d : Slot}
include h p
lemma Bc (i): (Row.B i,jet B (beta UnitV Ω (ket i)))∈ready V c d K := by
  rw [betaV,map_sum]; simp_rw [map_smul,on_ket]; exact f_bought V c d h p i
-- Compose `DD` with actions on m. f5 split arms via tensor formulas. cleaner generic Lemma execution.
omit h p
variable {α β γ η : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ]
lemma fork_cost (A : Cell α) (B : Cell β) (i j) (Ω) (Q : α×β→J η) :
    jet Q ((wings A B).beta Ω (ket (i,j))) = jet (fun k:α=>Q (k,j)) (A.beta Ω (ket i)) + jet (fun k:β=>Q (i,k)) (B.beta Ω (ket j)) := by
  have hx : jet Q ∘ₗ times'.flip (ket j)=jet (fun k:α=> Q (k,j)) := ket_ext fun t=>by simp
  have ht : jet Q ∘ₗ times' (ket i)=jet (fun k:β=> Q (i,k)) := ket_ext fun t=>by simp
  rw [← takes i j,optionB, split_legs, map_add]; exact congr_arg₂ _ (LinearMap.congr_fun hx _) (LinearMap.congr_fun ht _)
lemma monop (f : α⊕β→ J η) (U : J α): jet f (leftU U) = jet (fun i:α=> f (Sum.inl i)) U := by
  have H: jet f ∘ₗ leftU=jet (fun i:α=> f (.inl i)) := ket_ext fun i=>by simp [leftU]
  exact LinearMap.congr_fun H _
lemma monopol (f:α⊕β→ J η) (U : J β): jet f (rightU U) = jet (fun i:β=> f (.inr i)) U := by
  have H: jet f ∘ₗ rightU=jet (fun i:β=> f (.inr i)):=ket_ext fun i=>by simp [rightU]
  exact LinearMap.congr_fun H _
lemma motion (f:Axis → J η) (i Ω) : jet f (UnitV.beta Ω (ket i))=∑ j:Axis,(Ω.val j i : ℂ) • f j:= by rw [betaV,map_sum]; simp_rw [map_smul,on_ket]

include h p
lemma Tc (i) : (evalTf i,jet evalTf (PT1.beta Ω (ket i)))∈ready V c d K := by
  rcases i with ⟨j,k|k⟩ <;> rw [PT1,fork_cost]
  · have ht:= Lsmart (c:=c) (d:=d) h V p k _ (Bc h p V (c:=c) (d:=d) j) -- argument order
    rw [input1,monop,motion,motion]; change (L k (Cauchy.Row.B j), (∑ i:Axis, (Ω.val i j:ℂ) • L k (Cauchy.Row.B i)) + ∑ i:Axis,(Ω.val i k:ℂ) • (L i (Cauchy.Row.B j))) ∈ _
    rw [motion,costD,map_sum] at ht; simp_rw [map_smul] at ht; exact ht
  have ht:= Psmart (c:=c) (d:=d) h V p k _ (Bc h p V (c:=c) (d:=d) j); rw [input2,monopol,motion,motion]
  rw [motion,costD,map_sum] at ht; simp_rw [map_smul] at ht; exact ht
lemma UU (i j k : Axis):
    (foldP (i,Sum.inl (j,k)),jet foldP (PT2.beta Ω (ket (i,Sum.inl (j,k)))))∈ready V c d K := by
  rw [PT2,fork_cost, motion,input1,monop,Theta, fork_cost,motion,motion];
  have ht:=Tc h p V (c:=c) (d:=d) (i,.inl k)
  rw [PT1,fork_cost,input1,monop,motion,motion] at ht; have hv:=Lsmart h V c d p j _ ht
  rw [costD,map_add,map_sum,map_sum] at hv; simp_rw [map_smul] at hv
  rw [← add_assoc,add_right_comm]
  exact hv
lemma VV (i j k:Axis):
    (foldP (i,Sum.inr (Sum.inl (j,k))),jet foldP (PT2.beta Ω (ket (i,Sum.inr (Sum.inl (j,k))))))∈ready V c d K := by
  rw [PT2,fork_cost,motion,input2,monopol,input1,monop,Theta,fork_cost,motion,motion]
  have ht:=Tc h p V (c:=c) (d:=d) (i,.inr k); rw [PT1,fork_cost,input2,monopol,motion,motion] at ht; have hv:= Psmart h V c d p j _ ht
  rw [costD,map_add,map_sum,map_sum] at hv; simp_rw [map_smul] at hv
  rw [← add_assoc,add_right_comm]
  exact hv
lemma VS (i j k:Axis):
    (foldP (i,.inr (.inr (j,k))),jet foldP (PT2.beta Ω (ket (i,.inr (.inr (j,k))))))∈ready V c d K := by
  rw [PT2,fork_cost,motion,input2,monopol,input2,monopol,Theta,fork_cost,motion,motion]
  have ht:= Tc h p V (c:=c) (d:=d) (i,.inl k); rw [PT1,fork_cost,input1,monop,motion,motion] at ht; have hv:= Psmart h V c d p j _ ht
  rw [costD,map_add,map_sum,map_sum] at hv; simp_rw [map_smul] at hv
  rw [← add_assoc,add_right_comm]
  exact hv
lemma Vc (i): (foldP i,jet foldP (PT2.beta Ω (ket i)))∈ ready V c d K := by
  rcases i with ⟨j,i|i|i⟩
  · exact UU h p V j i.1 i.2
  · exact VV h p V j i.1 i.2
  exact VS h p V j i.1 i.2
end YM.GaugeFieldConstruction.Stage.Wide
