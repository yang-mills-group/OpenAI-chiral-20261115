import YM.SU5.FiniteGaugeData.Concord.Score
/-! # The step we take in the whole extraction. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin Afterglow.Journey Girt
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale

section transfer
variable {c f:Side}(g:Ratio c f)(A:StepData (More c) (More f))(j d k:ℕ)
variable (Q:Op SU.Slot)(M:Male)(h: Odd g.count.val)(q: Chi)(v β:ℝ)(l:Scree.Loom c)
local notation "T" => pushMark g A j Q M h q v β l
variable (h₁:A.patch.Branches A.kernel SU.group) (p:LaurentRadius j g.count d)(u:0<v)(s:2*v < firstRadius SU.group) (v':Measurable l)
local notation "U" => gathered g j Q M h q v
local notation "F" => Forest (ratio g)
include h₁ p u s v'
lemma step_add {X Y:Mark c}(t:Envelope X)(z:Envelope Y) : T (X+Y)= T X+T Y := by
  funext a
  have he (x:Mark c)(t:Envelope x) : Integrable (fun y:Orbit c=> A.density β a.1 y.1 • U x a (drawn l y)) (city c):= Env.integrableX (Env.scale (Env.along (slice_env A β h₁ a.1) measurable_fst) (Env.along (g:=fun x:Orbit c=>(a,drawn l x)) (env_gathered g j Q M h q v p u s x t) (measurable_const.prodMk (drawn_m l v')))) _
  have hW (t:Fields c) : gathered g j Q M h q v (X+Y) a t= U X a t+ U Y a t := by unfold gathered avgF before; simp_rw [Pi.add_apply,map_add,sum_add_distrib,smul_add]
  have hx (x:Mark c)(t:Envelope x) := outright g A j Q M h q v β l p v' h₁ u s x t a
  rw [Pi.add_apply,hx X t,hx Y z,←integral_add (he _ t) (he _ z), hx (X+Y) (show Envelope _ from Girt.kitE X Y (·+·) (by fun_prop) t z)]; simp_rw [hW,smul_add]
lemma step_smul {X:Mark c}(t:Envelope X)(r:ℂ) : T (r • X)= r • T X:=by
  funext a
  have he (x:Mark c)(t:Envelope x) := outright g A j Q M h q v β l p v' h₁ u s x t a
  have hz (x: Fields c) : U (r • X) a x= r • U X a x:=by
    unfold gathered avgF before; simp_rw [Pi.smul_apply,map_smul, ←smul_sum]; rw [smul_comm]
  rw [Pi.smul_apply,he _ t, he (r • X) (Girt.pole_w X _ (continuous_const (y:=r) |>.smul continuous_id) t)]; simp_rw [hz]; apply Eq.trans _ (integral_smul r _); exact integral_congr_ae (Eventually.of_forall fun i=> smul_comm _ _ _)
omit p u s v'
lemma step_unit : T 1=1:=by
  letI: Nonempty (Forest (ratio g)):= Tree.select (ratio g) h
  let L:= assembled g j Q M h q v l (1:Mark c)
  have hw(W:Fields f)(V: Pane c): L W V=1:=by
    unfold L Advance.assembled gathered avgF before
    simp_rw [Pi.one_apply,sub_one,sum_const,card_univ,← Nat.cast_smul_eq_nsmul (R:=ℝ)]
    have he:(Fintype.card (Forest (ratio g)):ℝ)≠0:=by positivity
    simp [inv_smul_smul₀ he]
  funext W; change linkLaw A β (L W) W.1=1; unfold linkLaw; simp_rw [hw]; rw [integral_smul_const,(A.isKernel h₁ β).total,one_smul]
end transfer

variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable (s:ℕ) {i k:ℕ}(p: PairIdx Y s i k) (S:Finset Cover)
local notation "R" => Λ.R
local notation "D" => aliasLaw Λ
local notation "n" => side Y i s
local notation "μ" k:max=> momentm Y i k
local notation "ν" => side Y i (s+1)

def seamWidth (Λ:Preparation)(l:ℕ) : ℕ := Λ.R.L.val*gross (aliasLaw Λ) (distanceLaw l) Λ.R.J
def swept (Λ:Preparation)(l:ℕ)(S:Finset Cover) := Satin.liner (S.image (fun a=> Λ.R.L.val • a)) (seamWidth Λ l)
local notation "S₁" => swept Λ l S
local notation "K" => tent Y H

local notation "Υ" => (Y.voyage i)
local notation "U" => (Υ).CapeT
local notation "X" => (Υ).X (Y.uv k)
local notation "A" => steps Λ.V (Y.ir i) Λ.block (Y.uv k)
local notation "G" => apt (Y.ir i) Λ.block Λ.R.L s

def haul (i k:ℕ) : Mark (side Y i s) → Mark (side Y i (s+1)) :=
  nextMark (j:=Λ.K.j) (ho:=Λ.R.odd_side) ((Y.voyage i).X (Y.uv k)).gram (Y.voyage i).CapeT Chi.canonical Λ.J.d (((Y.voyage i).X (Y.uv k)).wave) (steps Λ.V (Y.ir i) Λ.block (Y.uv k)) s
local notation "ψ"=> haul Y s i k

include p
lemma can_cane : 0<Λ.J.d ∧ 2*Λ.J.d < firstRadius SU.group := ((fullness Y i k p.1).cap_grant.grant s p.2).some.legal

lemma haul_add {F E:Mark (side Y i s)} (h:Envelope F)(t:Envelope E) : ψ (F+E)=ψ F+ψ E:= step_add G ((A) s) Λ.K.j (aliasLaw Λ) _ _ _ _ _ _ _ ((fullness Y i k p.1).cap_grant.branch s p.2) (Journey.legal _) (can_cane Y s p).1 (can_cane Y s p).2 ((Υ).ownership s).paid.bill h t
lemma haul_scale {F:Mark (side Y i s)} (h:Envelope F)(t:ℂ) : ψ (t • F)= t • ψ F:=step_smul G ((A) s) Λ.K.j (aliasLaw Λ) _ _ _ _ _ _ _ ((fullness Y i k p.1).cap_grant.branch s p.2) (Journey.legal _) (can_cane Y s p).1 (can_cane Y s p).2 ((Υ).ownership s).paid.bill h t
lemma haul_one : ψ 1 = 1:= step_unit G ((A) s) Λ.K.j _ _ _ _ _ _ _ ((fullness Y i k p.1).cap_grant.branch s p.2)

lemma package {b:Bool}{F:Mark (side Y i s)} (h:AtSupport b (region S (side Y i s)) F) : AtSupport b (region (swept Λ l S) (side Y i (s+1))) (ψ F):=by
  let a:= (fullness Y i k p.1).cap_grant
  have he:= surround G ((A) s) Λ.K.j ((X).wave s).val ((X).gram (s+1)).J.M (R).odd_side Chi.canonical Λ.J.d ((X).gram (s+1)).beta ((U) s) (show LaurentRadius Λ.K.j (R).L D from Journey.legal Λ) (((Υ).ownership s).paid.bill) (a.branch s p.2) (can_cane Y s p).1 (can_cane Y s p).2 _ h (tissue Y i s) (a.aligned s p.2)
  rw [show ((A) s).patch.J = (R).J from a.radius s p.2] at he
  exact he.mono (next_contains S _ n G)

lemma score_repeat (F: Mark (side Y i s)) (h:AtSupport false univ F) : Journey.compass Y i k s F=Journey.compass Y i k (s+1) (haul Y s i k F):= by
  have he:=single_num Λ.U (X).gram U Chi.canonical Λ.J.d (Y.uv k) (X).wave A (Journey.legal Λ) (fullness Y i k p.1).cap_grant h p.2
  unfold Journey.compass; rw [he,(X).balance s p.2.le,←(X).balance (s+1) p.2]; rfl

omit p
variable {S}
lemma can_pack : ∀ᶠ i:ℕ in atTop, Tipping (plaza (Λ:=Λ) S) (side Y i s) (VolumeCape.Dream.plot l).C ∧ Hosp (tips (swept Λ l S)) ((tent Y H).c (momentm Y i (s+1))) := by
  refine Eventually.and ?_ ((momentum Y (s+1)).eventually (suitable _ _))
  have h:= (momentum Y s).eventually (separates (tent Y H) (tips (porch (VolumeCape.Dream.plot l).C (plaza (Λ:=Λ) S))))
  exact h.mono (fun i p=> Eq.mp (congrArg (fun m=> Tipping (plaza (Λ:=Λ) S) m (VolumeCape.Dream.plot l).C) (terrain Y H (Y.ir i) s)) (show Tipping _ ((tent Y H).c (momentm Y i s)) _ from p))
variable (S)(t : Hosp (tips (swept Λ l S)) ((tent Y H).c (momentm Y i (s+1))))

local notation "cutm" => Copies.transport (terrain Y H (Y.ir i) (s+1))
include p t

def concert : Palette S →ₗ[ℂ] Palette (swept Λ l S) := by
  let F(u:Palette S) := nativeHere Y H i s S u
  let T : Palette S→ₗ[ℂ] active (swept Λ l S) (tent Y H) (momentm Y i (s+1)) :=
    { toFun := fun u=> ⟨(cutm).symm (ψ (F u)), Copies.certificate _|>.mpr (package Y s p S (nativeHere_support ..))⟩
      map_add' u v:= by
        apply Subtype.ext; change (cutm).symm (ψ (F (u+v)))= _+_
        rw [show F (u+v)=F u+F v from map_add (nativeHere Y H i s S) u v, haul_add Y s p (nativeHere_support ..).env (nativeHere_support ..).env,map_add]
      map_smul' a u:= by
        apply Subtype.ext; change (cutm).symm (ψ (F (a • u))) = a • _
        rw [show F (a • u)= a • F u from map_smul (nativeHere Y H i s S) a u, haul_scale Y s p (nativeHere_support ..).env,map_smul] }
  exact (paintMark (swept Λ l S) (tent Y H) t).toLinearMap.comp T

/-- Actual operator equality, not a calibration postulate. -/
theorem repertoire (F:Palette S): nativeHere Y H i (s+1) (swept Λ l S) (concert Y H s p S t F)= haul Y s i k (nativeHere Y H i s S F):=by
  unfold concert; let h : AtSupport false _ (ψ (nativeHere Y H i s S F)) := package Y s p S (nativeHere_support ..)
  let f:active (swept Λ l S) K (μ (s+1)):=⟨(cutm).symm (ψ (nativeHere Y H i s S F)),Copies.certificate _|>.mpr h⟩
  change cutm (native _ _ _ (paintMark _ K t f)) =_
  rw [exhibit]; exact (cutm).apply_symm_apply _

lemma solo (F:Palette S): sharply Y H i s k S F= sharply Y H i (s+1) k _ (concert Y H s p S t F):=by unfold sharply; rw [repertoire]; exact score_repeat Y s p _ ((nativeHere_support ..).mono (Finset.subset_univ _))
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.solo
