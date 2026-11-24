import YM.SU5.FiniteGaugeData.Cirrus.Saffron
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus.PavilionM
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe Maison Flute Mink
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)(Ω:Bench S)
variable {ι:Type}(G:Canopy H ι)(J K:Set ι)(U V:Set E4)(t:G.Token)(w:List G.Token)
local notation "D"=> G.Model S Ω
local notation "X"=> Effort S Ω G
local notation "E"=> G.lens S Ω
local notation "Ω₁"=>G.focus S Ω []
local notation "T₁"=> RToken G J U
local notation "Kₐ"=> Hull S Ω G
open Canopy Submodule
variable (A B:Effort S Ω G) (Pn:Boundary.Action H) (p:Mink.Poincare)(L:G.Arrival S Ω Pn)
local notation "T₂"=> DualR S Ω G
abbrev actW(p:Poincare): X:= emergeC G S Ω p Pn L.lift
abbrev actionAt (p:Mink.Poincare) (A : Effort S Ω G) : X := actW S Ω G Pn L p * A * actW S Ω G Pn L p⁻¹
local notation "W"=> actW S Ω G Pn L
local notation "Ξ"=>actionAt S Ω G Pn L
include L
lemma cost (x y:D): inner ℂ (E (W p x)) (E (W p y))=inner ℂ (E x) (E y):=by
 unfold actW; rw [←L.respect p,← L.respect p]; exact LinearIsometry.inner_map_map (show H →ₗᵢ[ℂ] H from { (Pn.V p).toLinearMap with norm_map':= fun x=> Pn.usual p x }) _ _
lemma κp : actW S Ω G Pn L p * W p⁻¹=1:=by ext1 x; change (W p) ((W p⁻¹) x)=x; exact Flip_inc ..
lemma τp : actW S Ω G Pn L p⁻¹ * W p=1:=by rw [← inv_inv p]; rw [inv_inv p]; exact (by -- simp double
    simpa only [inv_inv] using κp S Ω G Pn (p⁻¹) L)
lemma Wh (x:D) : W p⁻¹ (W p x)=x:= LinearMap.congr_fun (τp S Ω G Pn p L) x
lemma vω : actW S Ω G Pn L p Ω₁=Ω₁:= flight ..
lemma pitchAct (x:D) : Ξ p A (W p x)= W p (A x):=by
 change W p (A (W p⁻¹ (W p x)))=_; rw [Wh]
lemma inherits (v:DualR S Ω G A B): DualR S Ω G (Ξ p A) (Ξ p B):=by
 intro x y; rw [show x=W p (W p⁻¹ x) from (Flip_inc ..).symm, show y=W p (W p⁻¹ y) from (Flip_inc ..).symm,pitchAct,pitchAct,cost,cost]; exact v _ _
lemma returns : actionAt S Ω G Pn L p⁻¹ ( Ξ p A)=A:=by unfold actionAt; let e:= τp S Ω G Pn p L; rw [inv_inv,←mul_assoc,←mul_assoc,e,one_mul,mul_assoc,e,mul_one]
-- TS shift proof
omit L in
lemma sendsC(x:Test4): tsupport (Joint.push p x) ⊆ p.sends '' tsupport x:=by
 let f(z:E4):=Poincare.sends (p⁻¹) z; have hc:Continuous f:=by unfold f Poincare.sends; fun_prop
 have h: MapsTo f (tsupport (Joint.push p x)) (tsupport x):= MapsTo.closure (s:=support (Joint.push p x)) (t:=support x) (fun u p'=> ?_) hc; swap; · exact fun t=> p' ((Joint.push_at p x u).trans t)
 exact fun x e=> ⟨f x,h e,Poincare.emerges p x⟩
lemma keepsTag (u:t∈T₁) : travel G p t ∈ RToken G J (p.sends '' U):= by
 refine ⟨u.1,?_, (sendsC p t.2).trans (image_mono u.2.2)⟩; apply (u.2.1.image (show Continuous p.sends from by unfold Poincare.sends;fun_prop)).of_isClosed_subset (isClosed_tsupport _) (sendsC p t.2)
lemma climbs (v:A∈ Kₐ J U) : Ξ p A∈ Kₐ J (p.sends '' U):=by
 let P:=W p; let V:=W p⁻¹; let K:= Kₐ J (p.sends '' U);
 have hp(c:ℂ): Ξ p (algebraMap ℂ (X) c)=c•1:=by unfold actionAt; rw [Algebra.algebraMap_eq_smul_one, Algebra.mul_smul_comm,Algebra.smul_mul_assoc,mul_one,κp]
 have he(A B:X): Ξ p (A*B)= Ξ p A * Ξ p B:=by
   change P* _ * V=P*A * V*(P*B*V); have hp:V*P=1:=τp ..; nth_rw 1 [show A*B=A*1*B from (by rw [mul_one]), ← hp]; simp only [mul_assoc]
 refine Algebra.adjoin_induction (p:=fun u _=>Ξ p u∈ K) ?_ ?_ ?_ ?_ v
 · rintro _ ⟨t,x,rfl⟩; have he: actionAt S Ω G Pn L p (G.conduct S Ω t)= G.conduct S Ω (travel G p t):=LinearMap.ext fun x=> (costume G S Ω p t Pn L.lift (V x)).symm.trans (congrArg (G.conduct S Ω (travel G p t)) (Flip_inc ..)); rw [he]; exact seeds S Ω G J _ _ (keepsTag S Ω G J U t Pn p L x)
 · intro c; rw [hp]; exact K.smul_mem K.one_mem _
 · intro i j z u t v; change P*(i+j)*V∈K; rw [mul_add,add_mul]; exact K.add_mem t v
 intro i j z u t v; rw [he]; exact K.mul_mem t v
lemma trunk : A∈ Hull S Ω G J U ↔ actionAt S Ω G Pn L p A∈ Kₐ J (p.sends '' U):=by
 refine ⟨climbs S Ω G J U A Pn p L,fun v=>?_⟩
 have he:= climbs S Ω G J (p.sends '' U) _ Pn (p⁻¹) L v; rw [returns] at he; apply regi S Ω G J J (Poincare.sends (p⁻¹) '' _) U (_root_.subset_refl _) ?_ he; rintro x ⟨_,⟨x,u,rfl⟩,rfl⟩; rw [Poincare.unmade]; exact u
#print axioms trunk
#print axioms inherits
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus.PavilionM
