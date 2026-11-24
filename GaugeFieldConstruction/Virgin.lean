import GaugeFieldConstruction.Yields
/-
The actual spatial-jet indices hit the full real Gem and the first Maxwell-Live slot.
Proof avoids Fourier positivity on a tight time aperture.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 40000
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht.Vesper
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys Flux.One Lamp Conj
open Lattice CF CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart CF.Py.Rate.LocalLimit.Papal
open scoped Topology ContDiff BigOperators InnerProductSpace Classical
open HopeC CF.Buffered CF.Buffered.Lifted FlightFlux Fluxim TableF TableF.Lenten Layout Shield Wilson Raw
open U1 Gauge97
-- Divergence is exact negative of conventional (our d_j F_ij).
def breezeD : Sut→ₗ[ℝ] (Axis→ℝ) where
 toFun D i:= ∑ j:Axis, D.val j i j
 map_add' A B:=by ext1 i; change ∑ j, (A.val j i j+B.val j i j)=_; rw [sum_add_distrib]; try rfl
 map_smul' r A:=by ext1 i; change ∑ j,r • A.val j i j=_; rw [← smul_sum]; try rfl
def liveD : Submodule ℝ Sut:= LinearMap.ker breezeD
lemma white_D (D:Sut)(i:Axis): divWhite i D=breezeD D i:=by
 -- generic or Fin4 manual.P.enum
 let a:PlaqAxes:= ⟨(0,1),by decide⟩; let b:PlaqAxes:=⟨(0,2),by decide⟩; let c:PlaqAxes:=⟨(0,3),by decide⟩; let e:PlaqAxes:=⟨(1,2),by decide⟩; let f:PlaqAxes:=⟨(1,3),by decide⟩; let u:PlaqAxes:=⟨(2,3),by decide⟩
 have hv:(univ:Finset PlaqAxes)={a,b,c,e,f,u}:=by unfold a b c e f u; decide
 unfold divWhite; rw [hv]; change _=∑ j:Axis,D.val j i j; unfold a b c e f u
 repeat (first|rw [Finset.sum_insert (by decide)]|rw [Finset.sum_singleton])
 fin_cases i <;> simp (config:={decide:=true}) only [Fin.sum_univ_four,if_true,if_false]
 · change _= D.val 0 0 0+D.val 1 0 1+D.val 2 0 2+D.val 3 0 3; rw [F_slot0 D 0 0]; ring
 · change _= D.val 0 1 0+D.val 1 1 1+D.val 2 1 2+D.val 3 1 3; rw [F_slot0 D 1 1, F_neg D 0 1 0]; ring
 · change _= D.val 0 2 0+D.val 1 2 1+D.val 2 2 2+D.val 3 2 3; rw [F_slot0 D 2 2, F_neg D 0 2 0, F_neg D 1 2 1]; ring
 · change _= D.val 0 3 0+D.val 1 3 1+D.val 2 3 2+D.val 3 3 3; rw [F_slot0 D 3 3, F_neg D 0 3 0, F_neg D 1 3 1, F_neg D 2 3 2]; ring
lemma no_fee (i:GIndex) : E_D i∈ liveD:=by
 change breezeD (E_D i)=0; ext1 x; have he: ∑ j:Axis,Gder j (F j x)=0:=by
    apply loyalty; intro u; let a:= u.1.val.face u.2; change a.read _=0; rw [map_sum]
    refine Eq.trans (sum_congr rfl fun j _=>?_) (a.rigor.div x); rw [← LinearMap.comp_apply,a.frequency,LinearMap.smul_apply,a.read_F]; simp [power,Maxwell.skin]
 have ht:∑ j:Axis,Gder j (F x j)=0:=by
    conv=>lhs; rhs; intro j; rw [turnover x j, map_neg]
    rw [Finset.sum_neg_distrib,he,neg_zero]
 change ∑ j:Axis, (Gder j (F x j) i).re= _
 rw [←Complex.re_sum,←Finsupp.finsetSum_apply,ht]; rfl
def winkL (b:Bool)(a:S3) : GIndex:=by exact (b,⟨(a,0),fun _=>rfl⟩)
abbrev pipeL(b:Bool)(a:S3): Axis×Axis:= if b then ((cw a).castSucc,(ccw a).castSucc) else (τ,a.castSucc)
lemma wham (b:Bool)(a:S3):F (pipeL b a).1 (pipeL b a).2= ket (winkL b a):= by
 have he(b:Bool)(a:S3):G b a 0=ket (winkL b a):=picked_G (winkL b a)
 rw [←he]; cases b; · change F (Fin.last 3) (Fin.castSucc a)=_; simp only [F,Fin.lastCases_last,Fin.lastCases_castSucc]
 change F (Fin.castSucc (cw a)) (Fin.castSucc (ccw a)) = _; have hx(a:S3):cw (cw a)=ccw a:=by revert a; decide
 have hY(a:S3):ccw (cw a)=a:=by revert a; decide
 have hZ(a:S3):cw a≠ccw a:=by revert a; decide
 simp [F,hx,hY,hZ]
lemma wick_G (X:Gem): X=0 ↔ ∀ b a,X.val (pipeL b a).1 (pipeL b a).2=0:=by
 refine ⟨fun e b a=>e ▸ rfl,fun t=>?_⟩; apply Subtype.ext; funext i j
 let Y:=X.val; change Y i j=0
 have he(a): Y τ (Fin.castSucc a)=0:= t false a
 refine Fin.lastCases (i:=i) (Fin.lastCases (i:=j) (fluxZ ..) he) ?_
 intro m; refine Fin.lastCases (i:=j) ?_ ?_; · change X.val (Fin.castSucc m) τ=0; rw [flux_neg]; rw [show X.val τ _=0 from he m, neg_zero]
 intro k; by_cases e:m=k; · subst k; exact fluxZ ..
 have hx(a b:S3): a≠b → b=cw a ∨ a=cw b:=by revert a b; decide
 have h(a:S3): Y a.castSucc (cw a).castSucc=0:=by
    have he(c:S3):pipeL true (ccw c)=(c.castSucc,(cw c).castSucc):=by revert c; decide
    rw [show Y a.castSucc (cw a).castSucc=Y (pipeL true (ccw a)).1 (pipeL true (ccw a)).2 from by rw [he a]]; exact t true (ccw a)
 rcases hx m k e with p|p; · subst k; exact h m
 subst m; change X.val _ _=_; rw [flux_neg]; exact (congrArg Neg.neg (h k)).trans neg_zero
lemma wink_in : Injective (Function.uncurry winkL):=by intro a b h; exact Prod.ext (congrArg (fun i:GIndex=>i.1) h) (congrArg (fun x:GIndex=> x.2.val.1) h)
abbrev SayL:= Bool× S3
def beadL : Gem→ₗ[ℝ] (SayL→ℝ) where
 toFun A i:= A.val (pipeL i.1 i.2).1 (pipeL i.1 i.2).2
 map_add' A B:=rfl
 map_smul' r A:=rfl
lemma bead_g(X:Gem): X=∑ i:SayL,(beadL X i) • E_G (winkL i.1 i.2):=by
 have hx: LinearMap.ker beadL=⊥:= le_antisymm (fun i p=> (wick_G i).2 fun b a=>congrFun (show beadL i=0 from p) (b,a)) bot_le
 apply LinearMap.ker_eq_bot.mp hx; rw [map_sum, funext_iff]; intro i; simp_rw [Finset.sum_apply,map_smul, Pi.smul_apply]; have he(j:SayL): beadL (E_G (winkL j.1 j.2)) i=if (j=i) then (1:ℝ) else 0:=by
    let X:=winkL j.1 j.2; change (((F (pipeL i.1 i.2).1 (pipeL i.1 i.2).2) X)).re= _; rw [show F _ _ = _ from wham i.1 i.2]; by_cases p:j=i; · subst j; simp [X,ket]
    simp [X,ket,Finsupp.single_apply, show winkL i.1 i.2≠ winkL j.1 j.2 from wink_in.ne (Ne.symm p), p]
 simp_rw [he]; simp
end YM.GaugeFieldConstruction.Wick.Yacht.Vesper
end
