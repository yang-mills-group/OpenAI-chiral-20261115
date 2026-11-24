import YM.SU5.FiniteGaugeData.Stent.Agi
import YM.CF.Buffered.Lifted
import YM.CF.Buffered.PreSupport
import YM.SU5.FiniteGaugeData.Brique.Papaya
-- frame morphology -- the special site
set_option autoImplicit false
set_option maxHeartbeats 380000
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Buffered.Stent
open Function Filter Finset Lattice Laurent Fir Next.Free Bloch Lat Fock Rush Scroll MeasureTheory RG
open scoped Topology BigOperators Pointwise Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace Kronecker ENNReal
attribute [local instance] opCStarAlgebra
variable (R:Patch)
set_option quotPrecheck false
local notation "Λ"=> R.L
local notation "J"=> R.J
open Cube Stencil Tenant Tap Tulip Branch Spire Peaks Advance Skye Lifted CF.Stent
variable {x:Cover}
def rune: Cover:= step 0 + step 1
def specialM (L:Side): Cover:= mid L • (1:Cover) + rune
def zeroL (L:Side): Cover:= L.val • (nodeC (0:Cover))
abbrev boss (R: Patch):Cover:= specialM R.L
def growAge (o:Lattice.Order):Walk:= Lattice.route 0 (-(2 • rune)) o -- neg smul notation `-(2:ℕ)` invalid – change
lemma forward(L:Side)(ho:Odd L.val): nodeC (specialM L)=zeroL L+2 • rune:=by
 unfold nodeC zeroL specialM; rw [nodeC,smul_zero,zero_add,smul_add,two_smul ℕ (mid L • (1:Cover))]; have hp:= mid_double L ho; rw [←Nat.cast_smul_eq_nsmul ℤ L.val,← hp, add_smul, one_smul,two_mul,add_smul]; abel
lemma tail(L:Side)(o:Lattice.Order)(h:Odd L.val):stop (nodeC (specialM L)) (growAge o)= zeroL L:=by
 rw [forward L h,←add_zero (zeroL L+2 • rune),stop_trans]; unfold growAge; rw [Lattice.route_end]; abel
lemma limit_a(L:Side)(h:4≤L.val)(p:Odd L.val): lift (wrap L rune)= rune:=by
 apply lift_eq_iff.mpr; refine ⟨rfl, fun i=>?_⟩; obtain ⟨b,t⟩:= p; by_cases k:i=0 <;> by_cases s:i=1 <;> simp [rune,k,s] <;> omega
lemma limit_b(L:Side)(h:4≤L.val): -rune∈ box (L.val/2):=by rw [box_test]; constructor <;> intro i <;> by_cases p:i=0 <;> by_cases t:i=1 <;> simp [rune,t,p] <;> omega
variable {N P:Side}(G:Ratio N P)
local notation "Gk"=> ratio G
local notation "α"=> arm G
abbrev Yr(i:SpinIdx):Inta G:=((0:Site N),wrap G.count rune,i)
abbrev Yc(i:SpinIdx): Inta G:=((0:Site N),0,i)
lemma Launch : (ratio G).embed (node (0:Site N))= wrap (More P) (zeroL G.count) := by
 let W:= wrap (More N); have hb:node (0:Site N)=wrap _ (nodeC 0):=by rw [← node_of N,map_zero]
 rw [hb,Ratio.embed_wrap,zeroL]; rfl
variable (h:4≤G.count.val)(ho:Odd G.count.val)
include ho h
lemma Uport(i:SpinIdx): touch G true (Yr G i)= wrap (More P) (nodeC (specialM G.count)):=by
 rw [turnMap G true ho]; change (ratio G).embed (node (0:Site N))+wrap _ (2• (lift (wrap G.count rune)))=_; rw [Launch,limit_a G.count h ho, forward G.count ho, map_add]
lemma switched (i:SpinIdx)(b:SU.Slot): switchG G (Yr G i,b)= ((wrap P (specialM G.count),i),b):=by
 apply Prod.ext; swap; · rfl
 apply Prod.ext; swap; · rfl
 apply Tenant.needle; change node ((switchG G _).1.1)=node (wrap P (specialM G.count)); rw [show ∀ k',node (wrap P k')= wrap (More P) (nodeC k') from node_of P]; exact Uport G h ho i -- tune
lemma run_ae (i j:SpinIdx)(o:Lattice.Order): runD true false G.count (Yr G i).2 (Yc G j).2 0 o=growAge o:=by
 unfold Yr Yc growAge runD; simp [traceU,limit_a _ h ho] -- tune
omit h ho
-- No alias through offer. formulate expansion at P state.
lemma covers_H (L:Side)(D:ℕ)(h:2*D < L.val):∀ y∈ LabelSet D,wrap L y=0→ y=(0:Cover):=by
 intro i g z; have hz: lift (wrap L i)=i:=by apply lift_eq_iff.mpr; refine ⟨rfl,fun a=>?_⟩; have he:= box_test.mp ((mem_filter.mp g).1); obtain ⟨v,u⟩:= he; specialize v a; specialize u a; omega
 rw [←hz,z,lift_origin]
#print axioms switched
end YM.CF.Buffered.Stent
