import GaugeFieldConstruction.Potori
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
abbrev δN:=Op Tagφ
def θL (u:Bool×Tagφ):= fisc u.1 u.2
lemma θs : Bijective θL:=by
 constructor
 · rintro ⟨i,a,t⟩ ⟨j,v,m⟩ e; have hx: band i a=band j v:=congrArg Prod.fst (show (band i a,t)=(band j v,m) from e); have ht: (i,a)=(j,v):= (show ∀ i j,∀ a b:GaugeFieldConstruction.Cauchy.Spin,band i a=band j b→ (i,a)=(j,b) from by decide) i j a v hx; exact Prod.ext (congrArg (fun c:Bool×Spin=> c.1) ht) (Prod.ext (congrArg (fun c:Bool×Spin=>c.2) ht) (congrArg (fun x:Hove.Kt=> x.2) (show (band i a,t)=(band j v,m) from e))) -- ambiguous
 rintro ⟨a,t⟩; -- explicit exist for Sp idx via revert (decide not Prop exists)
 obtain ⟨b,v,p⟩: ∃ (b:Bool)(v:Cauchy.Spin),band b v=a:= (show ∀ a:SpinIdx,∃ (b:Bool)(v:Cauchy.Spin),band b v=a from by decide) a; exact ⟨(b,v,t),Prod.ext p rfl⟩
def θμ : Bool×Tagφ≃ Hove.Kt:= Equiv.ofBijective _ θs
def skim_L (b c:Bool):Pal→ₗ[ℂ] δN where
 toFun X:= X.submatrix (fisc b) (fisc c)
 map_add' _ _:=rfl
 map_smul' _ _:=rfl
def send_L(b c:Bool) (X:δN): Pal:= Matrix.of fun i j=> let a:=θμ.symm i; let e:=θμ.symm j; if b=a.1∧ c=e.1 then X a.2 e.2 else 0
lemma sendX(b c:Bool)(X:δN)(a e:Bool): skim_L a e (send_L b c X)= if (b,c)=(a,e) then X else 0:=by
 have hz(b:Bool)(i:Tagφ): θμ.symm (fisc b i)=(b,i):=Equiv.symm_apply_apply θμ (b,i)
 ext i j; change send_L b c X _ _=_; unfold send_L; rw [Matrix.of_apply]; simp_rw [hz]; split_ifs with p t l
 · rfl
 · exact (t (Prod.ext p.1 p.2)).elim
 · exact (p ⟨(Prod.mk.inj l).1,(Prod.mk.inj l).2⟩).elim
 rfl
lemma blank_A(b c:Bool)(X:δN):skim_L b c (send_L b c X)=X:=by rw [sendX,if_pos rfl]
lemma θU (P Q:Pal)(u:∀ b c,skim_L b c P=skim_L b c Q): P=Q:=by
 ext i j; obtain ⟨⟨b,r⟩,rfl⟩:= θs.2 i; obtain ⟨⟨c,t⟩,rfl⟩:= θs.2 j; exact Matrix.ext_iff.mpr (u b c) r t
lemma payoff(p c:Bool)(A B:Pal):skim_L p c (A*B)= skim_L p false A*skim_L false c B+ skim_L p true A*skim_L true c B:=by
 ext i j; rw [Matrix.add_apply,Matrix.mul_apply,Matrix.mul_apply]; let f(x:Hove.Kt):= A (fisc p i) x* B x (fisc c j)
 change (∑ x',f x')=_ -- via Matrix.mul_apply not rfl?
 rw [← Equiv.sum_comp θμ f, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]; try rfl
lemma leaf (A:Op SpinIdx)(B:Op SU.Slot)(b c:Bool):skim_L b c (A⊗ₖ B)= (block A b c) ⊗ₖ B:=by ext ⟨i,j⟩ ⟨v,l⟩; rfl
lemma κHigh(a b c:Bool):skim_L b c (baseF a)=if (b,c)=(a,a) then 1 else 0:=by
 ext ⟨i,j⟩ ⟨v,l⟩; let u:= fisc b (i,j); let x:=fisc c (v,l); let f(a:Bool):= if a then leadBᶜ else leadB; have hp(a):baseF a=cutM (f a):=by cases a; exact leadHigh.symm; exact leadLo
 have h(i:Spin)(j:SU.Slot)(b:Bool): fisc b (i,j) ∈ f a ↔ b=a:=by
    cases a; · change _∈leadB ↔ _; rw [mem_filter]; suffices (band b i ∈ plusHalf) ↔ b=false by simpa [fisc] using this -- tune
               exact (show ∀ (b:Bool)(i:Spin),band b i∈plusHalf ↔ b=false from by decide) b i
    change fisc b (i,j)∈ leadBᶜ↔ _; rw [mem_compl]; simp only [leadB,mem_filter,mem_univ,true_and]; exact (show ∀ b i, Cauchy.band b i∉plusHalf ↔ b=true from by decide) b i
 rw [hp]; change cutM (f a) u x= _; have he:u=x↔ b=c ∧ (i,j)=(v,l):=by rw [show (u=x)=(θL (b,i,j)=θL (c,v,l)) from rfl,θs.1.eq_iff,Prod.mk.injEq]
 unfold cutM; rw [Matrix.diagonal_apply]; by_cases g:(b,c)=(a,a)
 · let q:=Prod.mk.inj g; rw [if_pos g, Matrix.one_apply]; by_cases e:(i,j)=(v,l)
   · rw [if_pos (he.mpr ⟨q.1.trans q.2.symm,e⟩), if_pos ((h i j b).mpr q.1),if_pos e]
   rw [if_neg (fun h=>e (he.mp h).2),if_neg e]
 rw [if_neg g]; split_ifs with t p <;> first|rfl|skip
 exact (g (Prod.ext ((h i j b).1 p) ((he.1 t).1.symm.trans ((h i j b).1 p)))).elim
lemma KinS(g:SU.E)(b c:Bool): skim_L b c (KinX g)= if b=c then (1:M2) ⊗ₖ Matter.ma g else 0:=by
 rw [show KinX g=(1:Op SpinIdx) ⊗ₖ Matter.ma g from rfl,leaf]; split_ifs with p
 · subst c; rw [unit_block]
 have he: block (1:Op SpinIdx) b c=0:=by
    ext i j; change (1:Op SpinIdx) (band b i) (band c j)=_; rw [Matrix.one_apply]; apply if_neg; exact (show ∀ (i j:Spin)(b c:Bool),b ≠ c→band b i≠band c j from by decide) i j b c p
 rw [he]; simp
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
