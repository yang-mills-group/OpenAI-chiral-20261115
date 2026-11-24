/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Nacre.Helios
import YM.AnalyticNext.QUARTIC_MATCH.Rephase
import YM.Next.STATIONARY.Joint.Symmetry
set_option autoImplicit false
noncomputable section
namespace YM.CF.Kennel
open Function Filter Lattice RG Wilson Exterior Precision Bloch Laurent Tree Stationary
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f} (s : Site c)
private def tBond (s:Site n):Link G n→L[ℝ] Link G n:= edgeColor.symm.toContinuousLinearMap ∘L ContinuousLinearMap.pi (fun i:Edge (Site n)=> ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Edge (Site n)=>G.Color) (i.1+s,i.2)) ∘L edgeColor.toContinuousLinearMap
private lemma tBo(s:Site n)(x:Link G n)(i): edgeColor (tBond s x) i=edgeColor x (i.1+s,i.2):=by simp [tBond]
private def tTurn (s:Site n):BaseSites G n→L[ℝ] BaseSites G n:= gaugeColor.symm.toContinuousLinearMap ∘L ContinuousLinearMap.pi (fun i:Site n=> ContinuousLinearMap.proj (φ:=fun _ : Site n=>G.Color) (R:=ℝ) (i+s)) ∘L gaugeColor.toContinuousLinearMap
private lemma tTu(s:Site n)(x:BaseSites G n)(i): gaugeColor (tTurn s x) i=gaugeColor x (i+s):=by simp [tTurn]
def dragU(t:Site c)(U:Joint G c f):Joint G c f:=(Lattice.translate (S.ratio.embed t) U.1, fun i=> U.2 (i+t))
private def tJoint(s:Site c):Stationary.Vault G c f→L[ℝ]Stationary.Vault G c f := (tBond (S.ratio.embed s)).prodMap (tTurn s)
private lemma jJ(s:Site c)(x:Stationary.Vault G c f): tJoint (S:=S) s (tJoint (S:=S) (-s) x)= x:=by
 refine Prod.ext (edgeColor.injective (funext fun i=>?_)) (gaugeColor.injective (funext fun i=>?_)); change edgeColor (tBond _ (tBond _ _)) i= _; simp only [tBo,show S.ratio.embed (-s)=-S.ratio.embed s from map_neg S.ratio.root s]; simp -- tune
 change gaugeColor (tTurn _ (tTurn _ _)) i=_; rw [tTu,tTu]; simp
private lemma tMu(V:Config G c)(U: Joint G c f)(p:Clip)(R:PathData G)(q:S.Choices)(h:S.patch.Branches S.kernel G):
 muster S q p R (translate s V) (dragU (S:=S) s U)=muster S (S.withinChoice 1 s q) p R V U:=by
 have he:=AnalyticNext.QuarticMatch.Joint.field_channel p R h V U.1 U.2 1 s q; simp only [Lattice.pull_one,affine,Signed.act_one] at he; exact he
private lemma tCa(s:Site c)(U: Joint G c f)(x:Stationary.Vault G c f): dragU (S:=S) s (Stationary.extend x * U) = Stationary.extend (tJoint (S:=S) s x)*dragU (S:=S) s U:=by
 refine Prod.ext ?_ ?_; funext i; change (input _ _ _ _ * _)=input G f (tBond _ _) i*_; rw [input_color,input_color,tBo]; rfl
 funext i; change (switchSite _ _ * _)=(switchSite (tTurn s x.2) _*_); rw [switch_color,switch_color,tTu]; rfl
lemma sailT {p:Clip}{R:PathData G}(t:S.Choices)(V:Config G c)(U:Joint G c f)(h:S.patch.Branches S.kernel G)(k: Shell S (S.withinChoice 1 s t) p R V U): Shell S t p R (translate s V) (dragU (S:=S) s U):=by
 let H:= canon S (S.withinChoice 1 s t) p R V U; let A:= canon S t p R (translate s V) (dragU (S:=S) s U); let P:= tJoint (S:=S) (G:=G) (-s); have he:A= H∘ P:=by
    funext x; change muster _ _ _ _ _ (Stationary.extend x * _)= muster _ _ _ _ _ (Stationary.extend (P x)*U); conv_lhs=>rw [← jJ (S:=S) s x,← tCa]; exact tMu s _ _ _ _ t h
 change ContDiffAt ℝ ω A 0 ∧ fderiv ℝ A 0=0
 rw [he]; have hh : ContDiffAt ℝ ω H (P 0):=by rw [map_zero]; exact k.1
 refine ⟨hh.comp _ P.contDiff.contDiffAt,?_⟩
 rw [fderiv_comp _ (hh.differentiableAt (by simp)) P.differentiableAt,map_zero,show fderiv ℝ H 0=0 from k.2,ContinuousLinearMap.zero_comp]
lemma thawT {X : Type} [NormedAddCommGroup X][NormedSpace ℝ X]{U:X→Joint G c f}(x:X)(h:Thaw U x):Thaw (dragU (S:=S) s∘ U) x:=⟨fun _=>h.1 _,fun _=>h.2 _⟩
end YM.CF.Kennel
