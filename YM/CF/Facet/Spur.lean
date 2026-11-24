import YM.CF.Facet.North
import YM.CF.Facet.Gust
import YM.CF.Facet.Law
import YM.CF.Facet.Arc
import YM.CF.Facet.Hemp
import YM.CF.Facet.Horn
import YM.CF.Cour.Culm
import YM.CF.Tarn.Sold
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Facet
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena Tarn Reef
open scoped Topology BigOperators Classical ContDiff  InnerProductSpace
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
local notation "G₅"=> SU.group
open Cube Lat Rush Cour Scroll Laic Kennel Paige Spire Branch Broc Pec
variable {n B m X: Side}{T: Roam m X B}{G: Ratio (CSide m B) (CSide X B)}{p:Tube G₅ T}
variable{K:Teller G₅}{c f:Side}{S:StepData c f}{A:Finset (Site f)}{o:Site c}{s:Signed}{b:Site c}{x e d β a r σ w:ℝ}{l k:ℕ}
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {F:Tab T}{C V R Z η:ℝ}{Q: Msca m X B G e}{Φ:nomA m X B→ ℂ}{i:Site (More (CSide m B))}
variable{U U':Config G₅ (More (CSide m B))}{t:ℕ}
open Levier
variable{u:ℝ}{q:Chi}{h:0<e}
open Stationary Push.Loops
local instance : Nonempty (Tab S):=⟨⟨Classical.choice (Tree.select _ S.patch.odd_side),Classical.ofNonempty⟩⟩
lemma heads(H:Thu p x u l Q h K k η C a Z V R Φ)(P:Tab T) : let U:=franc p x q d u l Q h; let F:FileM (More (CSide m B)) G₅ := fun i=> Arena.aria fun v=> U v i; Head (More (CSide m B)) Reef.frolic F:=by
 intro Z' X'; let C₀:=CSide m B
 let H' := viz p x q d u l Q h H.funds H.ready H.tall H.pay H.ears H.sizes H.read H.tone
 have ht(g:Sweep C₀)(i: Site (More C₀))(V:Config G₅ (More C₀))(t:V∈pines G₅ _ u)(p:flashA g V∈pines G₅ _ u)(hq:wageZ g=true): X' i (flashA g V) =star (X' ((castX g).anon _ i) V):=by
    unfold X' Arena.aria; simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul,star_mul,star_inv₀,star_natCast, star_sum]; rw [mul_comm _ ( (Fintype.card (Tab T):ℂ)⁻¹)]; apply congrArg; let K:=Arena.spun T g.s (pasta g); rw [← Equiv.sum_comp K (fun P'=>Z' P' i (flashA g V))]; refine Finset.sum_congr rfl fun k _=>?_ ; have hx:= H' g H.fine i V k t p; unfold payZ at hx; rw [hq] at hx; exact hx
 let A:= pines G₅ (More C₀) u; let F(i:Axis):= Tarn.often u p P (Signed.mirror i) H.width
 have he:∀ᶠ z:InputZ G₅ (More C₀) in 𝓝 0,represent z∈ pines G₅ (More C₀) u:= (F 0).mono fun _ h=>h.1
 constructor
 · intro i; let j:Sweep C₀:= ray (N:=C₀) true (incX 1); have hp(y:InputZ G₅ (More C₀)): represent (Vsail Reef.frolic y)=flashA j (represent y):=by
      have h₁:=Reef.repr_c y; have he(V:Bkg (More C₀)): flashA j V=Reef.echo V:=by unfold flashA; change stir (xtra true) (castX _) V=_; rw [stir_e]; exact stir_d _
      rw [he]; exact h₁ -- tune
   let L:=Reef.cloak (Body 1 (More C₀)); have hP:L 0=0:=map_zero _; have hx:Tendsto (Vsail (n:=More C₀) Reef.frolic) (𝓝 0) (𝓝 0):=by change Tendsto L _ _; simpa using L.continuous.tendsto 0
   filter_upwards [he,hx.eventually he] with t h τ
   simp only [satX,Function.comp_apply]; rw [hp]; have hg:= ht j i (represent t) h (hp t ▸ τ) (by change true.xor (detX 1)=true; rw [det_i]; rfl)
   rw [stir_l,show affine j.s _ i=i from ?_] at hg; exact hg; change affine 1 ((assembly C₀).embed (wrap _ 0)) _=_; simp [affine,←Ratio.root_embed] -- tune
 intro i z; filter_upwards [F z] with t h; let a:= Signed.mirror z; let j:Sweep C₀:=ray (N:=C₀) false (incX a)
 let W:=represent t; have hf: flashA j W=pull a 0 W:=by unfold flashA; change stir _ _ _= _; rw [show j.charge=false from rfl,stir_e]; exact Ywin ..
 have hx:= ht j i W h.1 (hf.symm ▸ h.2) (by change false.xor (detX (Signed.mirror z))=true; rw [det_t]; rfl); rw [hf,stir_l] at hx; rw [show affine j.s _ i=a.act i from ?_] at hx; exact hx; change affine a ((assembly C₀).embed (wrap _ 0)) _=_; simp [affine,←Ratio.root_embed] -- tune
end YM.CF.Facet
