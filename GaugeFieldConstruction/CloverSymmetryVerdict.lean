import GaugeFieldConstruction.CloverSymmetryCovariant
import GaugeFieldConstruction.CloverSymmetryFilter
/-!
 # Final tensor-sector selection rules before choosing reconstruction. A whole kernel.
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
noncomputable section
namespace YM.GaugeFieldConstruction.Ember.Volumetric
open Calibration Raw Cauchy Phys Apit Stage Fathom Function Set Filter Module Empire Hulse Salam Palace
open Floor Carat Dawn Sailing Angles Points Bulb Analysis MeasureTheory Complex Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexConjugate ContDiff Kronecker InnerProductSpace
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
variable {S:City}{P:Axis→Across}{L:Sheds S P}{C:Supplies L}{u:ℕ→Carat}
namespace FirstPackMars.CloverRule
open Loft Cell NSF.Boundary NSF.Work.C20 NSF.LD
open YM.Boundary (Probe Probe.bar Joint Test4 Distn)
attribute [local instance] floatA floatY
attribute [local instance 30000] topx topg
open Stage.CloverSymmetry
variable (p:Ticket u C)
private lemma pay_through_st {Z:UV four}(U:FreeName four)(z:feat Z=(64:ℕ) • Z) : feat (U.c Z)=(64:ℕ) • U.c Z:=by
 change feat (U.c.toLinearMap Z) = _; rw [commuteFeat U.c.toLinearMap U.h,z,map_nsmul]; rfl
lemma origin_cost_st {Z:UV four}(U:FreeName four)(z:feat Z=(64:ℕ) • Z):∃ v∈ orbitSpin2, payFrame p v=U.c Z:=by
 let V:= (payFrame p).symm (U.c Z); have he:payFrame p V = U.c Z:=(payFrame p).apply_symm_apply _
 have hh: feat V = (64:ℕ) • V:= pay_through_st (p.path.caller four).swapped (pay_through_st U z)
 have hm:feat V=(64:ℂ) • V:=by rw [hh,← Nat.cast_smul_eq_nsmul ℂ]; norm_num
 refine ⟨V,?_,he⟩; nth_rw 1 [← inv_smul_smul₀ (by norm_num:(64:ℂ)≠0) V]; rw[←hm]; exact orbitSpin2.smul_mem _ (maskPass _)
lemma viaCost_st(Z:CogPV): ∃ v:CogPV, LowIncPV Z=(payFrame p) (LowIncPV v):=by
 let U:=p.path.caller three; have h(x:CogPV):(payFrame p) (LowIncPV x)= LowIncPV (U.c x):= by apply Calibration.inject four; rw[p.path.flight,LowFivePV,LowFivePV,p.path.flight]
 refine ⟨U.c.symm Z,?_⟩; rw [h,U.c.apply_symm_apply]
variable {Q B:CloudsL}{Shed:SurfCheckL Q}{Y:Wightman (SurfRimL Q)}(T:SurfCheckL B)
variable {W: NSF.Boundary.Surface (SurfRimL Q)} {j:(SurfRimL Q).RealSpin}{R:(SurfRimL Q).Rotation} {F:NSF.Boundary.Waves (SurfRimL Q)} {N: NSF.Boundary.Surface.Aurora W NSF.LD.drapeL}
include N
abbrev inGloomSt (G:SurfCheckL Q)(Z:CloudsL)(X Y:UV four):Prop:=
   (∀ x:Points 2,x∈conf 2→ sepCost Z x X Y=0) ∧
   (∀ x:NSF.Boundary.Full 2,x∈ NSF.Boundary.tube 2→ N.emit (G.TinCanL ∘ ![X,Y]) x=0) ∧
   W.W 2 (G.TinCanL ∘ ![X,Y])=0
local notation "Sl"=> inGloomSt (N:=N) Shed B
include T
lemma reapedGlow_st (V: SurfCheckL.boisterL p B)
    (u:F.Region (SurfRimL B))(a:F.NonTangentialFree W)(q:N.FullBody F) (U:FreeName four)(L:UV four)(Z:CogPV)(z:feat L=(64:ℕ) • L): (Sl) (U.c L) (LowIncPV Z) ∧ (Sl) (LowIncPV Z) (U.c L):=by
 obtain ⟨l,b,e⟩:= origin_cost_st p U z; obtain ⟨x,d⟩:=viaCost_st p Z
 rw [←e,d]
 have j(k:Points 2)(c:k∈conf 2): sepCost B k (payFrame p l) (payFrame p (LowIncPV x)) = 0:= strictCost p B T V k c b x
 have p'(A H)(t:∀ k∈conf 2, sepCost B k A H=0): Sl A H:= ⟨t,fun x h=> zeroPad B T Shed u q _ t x h,zeroDistrib B T Shed u a q _ t⟩
 exact ⟨p' _ _ j,p' _ _ (sepExchange B T _ _ j)⟩
omit N T
variable (h:Y.Realizes (W:=W) R j)
include h
local notation "phi"=>Y.operators.field
local notation "state"=>Y.operators.omega
lemma actualBill_one_st (V:ΧiMars)(f:Test4): inner ℂ state (phi (Shed.TinCanL V) f state)= W.W 1 (Shed.TinCanL ∘ ![V]) (YM.Boundary.Joint.materialize 1 ![f]):=by
 let v:Fin 1→Letter (SurfRimL Q):= fun i=> ((Shed.TinCanL ∘ ![V]) i,f); have hz:= h.meets (List.ofFn v);
 have hp: Prod.snd ∘ v= ![f]:=by ext1 i; fin_cases i; rfl
 rw [NSF.Work.C29.expectOfFn, hp] at hz; exact hz
lemma actualBill_two_st (X Y':ΧiMars)(f g:Test4): inner ℂ state (phi (Shed.TinCanL X) f (phi (Shed.TinCanL Y') g state))= W.W 2 (Shed.TinCanL ∘ ![X,Y']) (YM.Boundary.Joint.materialize 2 ![f,g]):=by
 let v: Fin 2→Letter (SurfRimL Q):=fun i=> ((Shed.TinCanL ∘ ![X,Y']) i, ![f,g] i); have hz:=h.meets (List.ofFn v); rw[NSF.Work.C29.expectOfFn] at hz; exact hz
#print axioms reapedGlow_st
#print axioms actualBill_two_st
end FirstPackMars.CloverRule
end YM.GaugeFieldConstruction.Ember.Volumetric
end
