import GaugeFieldConstruction.Fringes
set_option autoImplicit false
set_option maxHeartbeats 48000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden.MastTin.ArtCart
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
open Buffered Lifted Girt Skye Window Vale
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {G H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick.Yacht.Vesper Violets
-- Epoch hull as quadratures. standard cost coupons
open scoped Kronecker
open YM.GaugeFieldConstruction
variable (x:Cover)(w:300<n.val)
namespace BluffV
open Cauchy
local instance : AddCommGroup ↥P14:= PackP.G.toAddCommGroup
local instance : AddCommGroup ↥P25:= PackM.G.toAddCommGroup
local instance : Module ℂ ↥P14:= PackP.S.toModule
local instance : Module ℂ ↥P25:= PackM.S.toModule
open Row Phys
open Matter (FlavorIndex)
local notation "Fidx"=>FlavorIndex
local notation "FileP" => Fidx → J Row.f
abbrev shelfV (U:Submodule ℂ (J Row.f)):Submodule ℂ FileP:= Submodule.pi Set.univ (fun _ => U)
def pureS_ (i:FactIx)(x:FileP): FileP:= fun k=> figV i (x k)
variable {X Y:Type}[AddCommGroup X] [Module ℂ X] [AddCommGroup Y][Module ℂ Y]
-- recover common shell functions by injective factoring
lemma π_TLS (f:X→ₗ[ℂ]Y) (h:Injective f)(g:↥P03→ₗ[ℂ]Y)(u:LinearMap.range g≤ LinearMap.range f):∃ l:↥P03→ₗ[ℂ]X,f.comp l=g:=by
 obtain ⟨L,a⟩:= LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.mpr h); refine ⟨L.comp g,LinearMap.ext fun x=>?_⟩; obtain ⟨z,q⟩:=u (show g x∈ LinearMap.range g from ⟨x,rfl⟩); rw [LinearMap.comp_apply,LinearMap.comp_apply,← q, ← LinearMap.comp_apply L, a]; rfl -- tune
variable {Z:Type}[AddCommGroup Z][Module ℂ Z]
noncomputable def cashF (P:Z→ₗ[ℂ]Y)(f:X→ₗ[ℂ]Y)(u:Injective f) : Z→ₗ[ℂ]X:=((LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.mpr u)).choose).comp P
lemma cashX(P:Z→ₗ[ℂ]Y)(f:X→ₗ[ℂ]Y)(u:Injective f)(x:Z)(y:X)(v:P x=f y):cashF P f u x=y:=by unfold cashF; rw [LinearMap.comp_apply,v]; exact LinearMap.congr_fun ((LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.mpr u)).choose_spec) y
-- special.
def symf3 : ↥P03 →ₗ[ℂ] FileP:=cashF heelY graph_f ffaith
def symf4 : ↥P14 →ₗ[ℂ] FileP:=cashF μPhi4 graph_f ffaith
def symf5 : ↥P25 →ₗ[ℂ] FileP:=cashF μPhi5 graph_f ffaith
lemma TalΦ0 (a:Axis)(k:Fidx): heelY (alloy a k)=graph_f (single_S k (Row.B a)):= (starφ a k).trans (scroll_S ..).symm
lemma TalΦ1(a:Axis)(k:Fidx)(i:FactIx): μPhi4 (spikeV i (alloy a k))=graph_f (single_S k (figV i (Row.B a))):=by rw [scaleG,TalΦ0, scroll_S,scroll_S,mirth]
lemma TalΦ2(a: Axis)(k:Fidx)(i j: FactIx): μPhi5 (peakV i j (alloy a k))=graph_f (single_S k (figV i (figV j (Row.B a)))):=by rw [scaleK,TalΦ0,scroll_S,scroll_S,mirth, mirth]
lemma TΦ(a:Axis)(k:Fidx):symf3 (alloy a k)=single_S k (Row.B a):=cashX _ _ _ _ _ (TalΦ0 ..) -- dots with end?
lemma TΦs(a:Axis)(k:Fidx)(i:FactIx): symf4 (spikeV i (alloy a k))=single_S k (figV i (Row.B a)):=cashX _ _ _ _ _ (TalΦ1 ..)
lemma TΦp(a:Axis)(k:Fidx)(i j:FactIx):symf5 (peakV i j (alloy a k))=single_S k (figV i (figV j (Row.B a))):=cashX _ _ _ _ _ (TalΦ2 ..)
lemma potterS (i:FactIx)(f:LinearMap.range (tipSpike i)):True:=trivial -- simplify
-- generator spans off-shell.definite.
abbrev rayone(j:FactIx×Axis×Fidx): P14:=spikeV j.1 (alloy j.2.1 j.2.2)
abbrev raytwo(j:FactIx×FactIx×Axis×Fidx): P25:=peakV j.1 j.2.1 (alloy j.2.2.1 j.2.2.2)
lemma revAir (p:P14):p∈Submodule.span ℂ (Set.range rayone):=by
 let U:=Submodule.span ℂ (Set.range rayone)
 have he(i:FactIx)(p:P03):tipSpike i p∈U:=by
    have hp:Submodule.span ℂ (Set.range (Function.uncurry alloy)) ≤ U.comap (tipSpike i):=by apply Submodule.span_le.mpr; rintro x ⟨t,rfl⟩; exact Submodule.subset_span ⟨(i,t),rfl⟩ -- change
    exact hp (crests p)
 rw [spikeBus p]; exact Submodule.sum_mem _ fun i _=> he i _
lemma reverb (p:P25): p∈Submodule.span ℂ (Set.range raytwo):=by
 let W:= Submodule.span ℂ (Set.range raytwo); have he(i j:FactIx)(p:P03):tipPeak i j p∈W:=by
    have hp:Submodule.span ℂ (Set.range (Function.uncurry alloy)) ≤ W.comap (tipPeak i j):=by apply Submodule.span_le.mpr; rintro x ⟨t,rfl⟩; exact Submodule.subset_span ⟨(i,j,t),rfl⟩
    exact hp (crests p)
 rw [peakBus p]; exact Submodule.sum_mem _ fun i _=> W.smul_mem _ (he i.1 i.2 _)
lemma spanXq{ι:Type}{b:ι→X}(h:∀ x:X,x∈ Submodule.span ℂ (Set.range b))(f g:X→ₗ[ℂ]Y)(e:∀ i,f (b i)= g (b i)) (x:X) : f x=g x:=by
 apply Submodule.span_induction (p:=fun x _=> f x=g x) ?_ ?_ ?_ ?_ (h x)
 · rintro x ⟨i,rfl⟩; exact e i
 · simp
 · intro x y h s g l; rw [map_add,map_add,g,l]
 intro a x p u; rw [map_smul,map_smul,u]
lemma LiftF3 (p:P03): heelY p=graph_f (symf3 p):=by
 apply Submodule.span_induction (p:=fun x _=> heelY x= graph_f (symf3 x)) ?_ ?_ ?_ ?_ (crests p)
 · rintro x ⟨⟨i,j⟩,rfl⟩; simp only [Function.uncurry_apply_pair, TΦ]; exact TalΦ0 ..
 · rw [map_zero,map_zero,map_zero]
 · intro x y h H q u; rw [map_add,map_add,map_add,q,u]
 intro a x l t; rw [map_smul,map_smul,map_smul,t]
lemma LiftF4(p:P14): μPhi4 p=graph_f (symf4 p):=by
 apply Submodule.span_induction (p:=fun x _=> μPhi4 x= graph_f (symf4 x)) ?_ ?_ ?_ ?_ (revAir p)
 · rintro x ⟨⟨i,a,j⟩,rfl⟩; unfold rayone; rw [TΦs]; exact TalΦ1 ..
 · rw [map_zero,map_zero,map_zero]
 · intro x y h H q u; rw [map_add,map_add,map_add,q,u]
 intro a x l t; rw [map_smul,map_smul,map_smul,t]
set_option maxHeartbeats 260000 in
lemma LiftF5(p:P25):μPhi5 p=graph_f (symf5 p):=by
 apply Submodule.span_induction (p:=fun x _=> μPhi5 x= graph_f (symf5 x)) ?_ ?_ ?_ ?_ (reverb p)
 · rintro x ⟨⟨a,i,v,j⟩,rfl⟩; unfold raytwo; rw [TΦp]; exact TalΦ2 ..
 · rw [map_zero,map_zero,map_zero]
 · intro x y h H q u; rw [map_add,map_add,map_add,q,u]
 intro a x l t; rw [map_smul,map_smul,map_smul,t]
lemma fridge (a:Submodule ℂ (J Row.f))(i:Fidx)(x:J Row.f)(h:x∈a): single_S i x∈ shelfV a:=by
 intro j _; change (Pi.single i x:FileP) j∈ a; rw [Pi.single_apply]; split <;> first| exact h|exact a.zero_mem
lemma coffeeV (U:Submodule ℂ FileP) {A:Type}[Fintype A](f:A→ J Row.f)(p:∀ x y,single_S x (f y)∈U):shelfV (Record.space f) ≤ U:=by
 intro v e; have ht(i:Fidx): v i∈ Record.space f:=e _ (Set.mem_univ _); have hx(i:Fidx):single_S i (v i)∈ U:=by
    let L:= U.comap (single_S i); apply (show Record.space f ≤ L from ?_) (ht i); unfold Record.space; rw [Fintype.range_linearCombination]; apply Submodule.span_le.mpr; rintro x ⟨j,rfl⟩; exact p i j -- tune apply
 rw [show v=∑ i:Fidx, single_S i (v i) from (by ext1 j; rw [Finset.sum_apply]; simp [single_S,Pi.single_apply])]; exact Submodule.sum_mem _ fun i _=> hx i
lemma wicked {ι:Type}{b:ι→X}(h:∀ x:X,x∈Submodule.span ℂ (Set.range b))(P:X→ₗ[ℂ] Y)(a:Submodule ℂ Y)(p:∀ i,P (b i)∈a): LinearMap.range P ≤ a:=by have ht:Submodule.span ℂ (Set.range b)≤ a.comap P:=Submodule.span_le.mpr fun _ ⟨j,e⟩=>e ▸ p j; rintro i ⟨j,rfl⟩; exact ht (h j) -- tune
lemma sch3:LinearMap.range symf3=shelfV (Record.space Row.B):=by
 refine le_antisymm (wicked crests _ _ (fun ⟨i,t⟩=>?_)) (coffeeV _ _ fun i j=> ⟨_,TΦ j i⟩)
 change symf3 (alloy i t)∈_; rw [TΦ]; exact fridge _ _ _ (memo_U _)
lemma halo1{v:Axis}(u:Axis)(j:FactIx)(a:Fidx):single_S a (figV j (Row.B u))∈LinearMap.range symf4:=⟨_,TΦs u a j⟩
lemma llegaS (X:Submodule ℂ FileP)(i:Axis)(p:Fidx)(f:J Row.f)(h:∀ b:Bool,single_S p (figV (b,i) f)∈X): single_S p (P_f i f)∈X ∧ single_S p (L i f)∈X:=by rw [←fig_s,←fig_r]; simp only [LinearMap.add_apply,map_add,LinearMap.neg_apply,map_neg]; exact ⟨X.add_mem (h _) (h _), X.add_mem (X.neg_mem (h _)) (h _)⟩
lemma sch4:LinearMap.range symf4=shelfV (Record.space evalTf):=by
 refine le_antisymm (wicked revAir _ _ (fun ⟨t,i,k⟩=>?_)) (coffeeV _ _ fun i j=>?_)
 · change symf4 (spikeV t (alloy i k))∈ _; rw [TΦs]; exact fridge _ _ _ (earn4 ..)
 rcases j with ⟨v,l|l⟩; exact (llegaS _ l i _ (fun b=>halo1 (v:=v) v (b,l) i)).2; exact (llegaS _ l i _ (fun b=>halo1 (v:=v) v (b,l) i)).1
lemma buy5(X:Raw.F4)(i:FactIx)(u:Fidx): single_S u (figV i (evalTf X))∈ LinearMap.range symf5:=by
 let K:=LinearMap.range symf5; rcases X with ⟨a,h|h⟩; · change single_S _ (figV _ (L _ _))∈ _; rw [←fig_r]; simp only [LinearMap.add_apply,map_add,LinearMap.neg_apply,map_neg]; exact K.add_mem (K.neg_mem ⟨_,TΦp ..⟩) ⟨_,TΦp ..⟩ -- tuning
 change single_S _ (figV _ (P_f _ _))∈ _; rw [←fig_s]; simp only [LinearMap.add_apply,map_add]; exact K.add_mem ⟨_,TΦp ..⟩ ⟨_,TΦp ..⟩
lemma sch5:LinearMap.range symf5=shelfV (Record.space evalF):=by
 refine le_antisymm (wicked reverb _ _ (fun ⟨t,v,i,k⟩=>?_)) (coffeeV _ _ fun i j=>?_)
 · change symf5 (peakV t v (alloy i k))∈_; rw [TΦp]; exact fridge _ _ _ (spend5 _ (earn4 ..) _)
 rcases j with ⟨u,h|l|l⟩; · exact (llegaS _ h.val.1 i _ (fun b=>buy5 (u,Sum.inl h.val.2) (b,h.val.1) i)).2
 · exact (llegaS _ l.val.1 i _ (fun b=>buy5 (u,Sum.inr l.val.2) (b,l.val.1) i)).1
 exact (llegaS _ l.1 i _ (fun b=>buy5 (u,Sum.inl l.2) (b,l.1) i)).1
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
