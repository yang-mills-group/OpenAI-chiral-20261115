import YM.SU5.FiniteGaugeData.Signal.Soloist
/-! # Non-factorization of moments in charged classes. -/
set_option autoImplicit false
set_option linter.flexible false
set_option maxHeartbeats 760000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Signal
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Afterglow Buffered.Advance Reef Hom Tenant Branch Buffered.Concord Buffered.Afterglow.Satin Lifted
open MeasureTheory Push.SectorMeasure Girt
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate Pointwise
attribute [local instance] opCStarAlgebra
open Supplies Sparkle Sparkle.Condense Sparkle.Portage Sparkle.Circuit Pastel Momentum Furnace
open Scherzo Kinetic Play Py Py.Rate LocalLimit Preparation Skyscraper IgnoreFog Vale Period
open Buffered.Reliance Buffered.Reliance.ShortWave Afterglow Afterglow.Journey
open Boon Graph Pressure Esti Jade.Earn Phase CF.Laic CF.Ember
open Escalator Concord Boon Parfume
namespace Ovation
variable {P:Preparation}{k' d q r Ul b kd l':ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l'))(H:Real.exp 1 ≤ P.x){g C Ω z a:ℝ}
variable {i k:ℕ→ℕ}{I:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}{E':ℕ→Buffered.Family (tent Y H)→ℂ}
local notation "Λ"=> tent Y H
variable (s:ℕ){o: Cover}
local notation "U★"=> (SculptureBirth P g k')
local notation "Ur"=> (high P Ul d)
local notation "ν₀" n:max=> momentm Y n s
variable (V: Universal Y H i k I E') (S T:Finset Cover) (J:List Cover) (l:SU.Slot)
local notation "Ωf"=> family l
variable {f:Buffered.Family (tent Y H)}(u:Shelter T S J)(v:J≠[])
include u v
theorem unplugged (n d:ℕ)(h:s ≤ Y.uv d)(r: Hosp T ((tent Y H).c (momentm Y n s)))(p:f∈ Parfume.price (tent Y H) (family l) S J): sharp Y H s n d f=0:=by
 let N:=side Y n s; let K:= (Y.sturdy n d); have p0: Plum.Rotate (denZ (K.E s) P.U (K.Y s)):=by
    intro g x; let W:= Carousel.loomActs P.V 1 2 6 P.N0 P.J Chi.canonical P.h P.R0 P.δ K s; let Q:=P.J.gran.trans (K.roof s).size; let X:= Carousel.credit_rule P.V 1 2 6 P.N0 P.J Chi.canonical P.h P.R0 P.δ K s h; exact Girt.sweep (K.E s) (K.legal s (h.trans K.probed)) X.leanJ.1 (K.Y s) P.J.n W x g P.W.pearl P.V.note Q (by rw [P.kJ]; omega)
 change markedRead _ (K.Y s) (denZ (K.E s) P.U (K.Y s)) / partitionZ (K.E s) _ _= _; rw [show markedRead (Journey.send Y H n s (f (momentm Y n s))) (K.Y s) (denZ (K.E s) P.U (K.Y s))= 0 from Transit.conceded (K:=tent Y H) (n:=(momentm Y n s)) (L₁:=K.Y s) (terrain Y H (Y.ir n) s) S T J f l u v p r p0] -- may not find Journey.send rw, annotate
 exact zero_div _
include V
lemma vacated (p:f∈Parfume.price (tent Y H) (family l) S J): ((∀ᶠ n:ℕ in atTop,I s f n=0) ∧ E' s f=0):=by
 let h:= V.together s f (show TestFamily (tent Y H) true f from (show f∈ junior Λ from also Λ ((show InTest Λ true T false f ∧_ from Parfume.stern Λ Ωf S T J u.1 u.2.1 p).1)))
 have p1 : ∀ᶠ n:ℕ in atTop, I s f n=0:= by
    filter_upwards [(momentum Y s).eventually (suitable T (tent Y H))] with n w; apply tendsto_nhds_unique (h.inner n); exact tendsto_const_nhds.congr' ((Y.uv_grows.comp V.pick.grow_k).tendsto_atTop.eventually_ge_atTop s|>.mono (fun d p1=> (unplugged Y H s S T J l u v n (k d) p1 w p).symm))
 exact ⟨p1,tendsto_nhds_unique h.periods (tendsto_const_nhds.congr' ((V.pick.grow_i.tendsto_atTop.eventually p1).mono (fun _ p=>p.symm)))⟩

/-- `cross_currency` criterion: on this same launch E and actual charged sector 
exists ℋ-coefficient giving nonfactorizable moment relative to first link and standalone CAR
matter part. `Effect` itself needn't be simple. -/
lemma cross_currency (p:f∈ Flying (tent Y H) (family l) S T J)(A:E' s f≠0): ∃ (g:LinksC→ℂ)(x:Buffered.Family (tent Y H)), Soft T g ∧ x∈ Parfume.price (tent Y H) (family l) S J ∧ E' s x=0 ∧ E' s ((stucco (tent Y H) g)* x) ≠ E' s (stucco (tent Y H) g)* E' s x :=by
 by_contra! h; have hg(z): z∈ Flying Λ Ωf S T J → E' s z=0:=fun hz=> by
   have hv: ∀ f : Buffered.Family (tent Y H), f∈ Flying Λ Ωf S T J→ f∈ junior Λ:=fun f t=>also Λ ((secure Λ Ωf S T J u.1 u.2.1 t).1)
   let U:=intake Y H s V; have hh(f:junior Λ): E' s f.val= U f:= (intake_eq Y H s V f).symm
   induction hz using Submodule.span_induction with
   | mem x p=>
      obtain ⟨g,t,v',u',rfl⟩:= p; have hp:= (vacated Y H s V S T J l u v u').2; rw [h g v' t u' hp,hp,mul_zero]
   | zero=> exact (hh 0).trans (map_zero U)
   | smul a f p v=>
      let g:junior Λ:= ⟨f,hv f p⟩; have hp:= hh (a • g); rw [map_smul] at hp; exact hp.trans (by rw [←hh g,v, smul_zero]) -- v rewrite `g.val`
   | add x y p q a b=>
      let g:junior Λ:=⟨x,hv x p⟩; let f:junior Λ:=⟨y,hv y q⟩; have hp:= hh (g+f); rw [map_add] at hp; exact hp.trans (by rw [←hh g,←hh f]; exact (congrArg₂ (·+·) a b).trans (zero_add 0))
 exact A (hg _ p)
end Ovation
end YM.CF.Signal
#print axioms YM.CF.Signal.Ovation.cross_currency
