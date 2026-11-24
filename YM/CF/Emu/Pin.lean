import YM.CF.Emu.Worth
import YM.CF.Reed.Play
import Mathlib.Analysis.Convex.Integral
set_option autoImplicit false
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Pic Nova Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc MeasureTheory Vale RG Wilson Scree Skye Pastry
open Reed (Fine)
variable {α:Type*}{N:Side}{o:Site N}{L B:Side}{j n:ℕ}{O:Odd L.val}{Y:Pricing j L O (Thread j)}{e b c v K a l r τ w u:ℝ}{P:Grasp Y B e}{H:Pearl P}{m:Side}{f:ℕ→Side}{R T W:ℕ→ℝ}
-- verify readers really in chosen algebra after averaging. no mirror pension assumed.
def halfS (N:Side): Finset (Single N):=univ.filter fun i=> i.1.2∈ plusHalf
lemma upper_q(N:Side): tickA N=cutM (halfS N):=by
 ext i j; rw [wing_m,cutM,Matrix.diagonal_apply]; by_cases e:i=j<;>simp [halfS,e]
def knotS {α:Type*}: List α→ Bool
 | [] => false
 | _::t=> Bool.xor true (knotS t)
lemma keyQ(x:Reader0 (Single N))(v:KeyT x (tickA N)): Reed.Fine (halfS N) univ true (ton x):=by
 rcases x with ⟨b,x⟩; unfold KeyT at v; rw [upper_q] at v; cases b
 · change Fine _ _ _ (create x); rw [create_def]; apply Fine.sumF; intro i _; have he:= Fine.seed (s:=halfS N) i (mem_univ _); by_cases h:i∈ halfS N
   · rw [show (Reed.think _).term i=put i from if_pos h] at he; exact he.scale _
   have hp : x.ofLp i=0:=by nth_rw 1 [← (show acts _ _=x from v)]; rw [cut_apply,if_neg h]
   rw [hp,zero_smul]; exact .empty _
 change Fine _ _ _ (remove x); rw [remove_def]; apply Fine.sumF; intro i _; have he:= Fine.seed (s:=halfS N) i (mem_univ _); by_cases h:i∈ halfS N
 · have hx:acts (cutM (halfS N)) x=0:=v; have hv:x.ofLp i=0:=by have ht:= congr_arg (fun y:Ket _ =>y.ofLp i) hx; simp only [cut_apply,if_pos h] at ht; exact ht
   rw [hv,star_zero,zero_smul]; exact .empty _
 rw [show (Reed.think _).term i= -takeF i from if_neg h] at he; exact (show Fine (halfS N) univ true (takeF i) from by simpa using he.scale (-1)).scale _
lemma paw_f (o:Site N)(U:Bkg (More N))(R:ℝ)(a:α→TagT)(J:List α): Fine (halfS N) univ (knotS J) (muni o U R a J):=by
 have hp(t): ∀ L:List α,Fine (halfS N) univ (knotS L) (zoneA o U t R a L):=by intro L; induction L with | nil=>exact Fine.one| cons i j ih=> exact (keyQ _ (nac_k o U t R (a i))).grow ih
 let Q:Submodule ℝ (FC (Single N)):= { carrier:={A:FC (Single N) | Fine (halfS N) univ (knotS J) A}, zero_mem':=Fine.empty _, add_mem':=fun {_ _} hx hy=> Fine.add hx hy, smul_mem':=fun c A h=> show Fine _ _ _ _ from (show (c:ℂ) • A=c • A from (by ext; simp [Complex.real_smul])) ▸ Fine.scale h (c:ℂ) } -- cast equality orientation
 change _∈ Q; exact Convex.integral_mem Q.convex Q.closed_of_finiteDimensional (ae_of_all _ fun a=>hp a _) (payI o U R a J)
local notation "N'"=> CSide m B
variable (D:Span H K b v c l r n)
-- use actual Wilson overlap / anticut. rectangular.
def plantH (U:Bkg (More N)):Op (Single N):= love N (frame matter (links U) (anticut N)).overlap
include D
lemma touchS(M:Bkg (Domain m B))(u:n≤(N').val)(p:Guard M e): plantH (N:=N') M * spar j firstM M=cutM (halfS N') * spar j firstM M:=by
 rw [frame_init P.topB P.baseY (P.couture (D.plan _ u).1 firstM) p]; rw [←upper_q]; unfold tickA plantH; let U:=frame matter (links M) (northZ m B); let L:=Phase.lens m B (northZ m B) M; let V:= love N'
 change V U.overlap*V L=V (cutM (upperP _))* V L; rw [←map_mul,←map_mul]; exact congrArg V (Reed.kinetic p P.baseY _)
lemma artQ (U:Bkg (Domain m B))(u:n≤(N').val)(p:Guard U e)(V:UNI (Single N'))(S: Finset (Single N'))(H:spar j firstM U=twist V (cutM S)) : let A:=halfS N'; let I:= Single N'; Reed.chemical ((plantH U)*V.val) A S=Reed.chemical V.val A S∧ ∃ z:ℂ,‖z‖=1∧∀ X:FC (Single (CSide m B)),Reed.Plain X→ z*Reed.spell (Reed.syms A) V.val A S X=inner ℂ (mateK N') (acts ((Reed.think A).eval X) (changeM (m:=m) P U firstM)):=by
 intro A I
 let P':= spar j firstM U; let C: Wave I:= changeM P U firstM; let F:= plantH U
 have ht:P'*V.val=V.val*cutM S:=by unfold P'; rw [H]; exact twist_product ..
 have hc:F*P'=cutM A*P':=touchS D U u p
 have hv:F*V.val*cutM S=cutM A*V.val*cutM S:=by rw [mul_assoc,mul_assoc,← ht,← mul_assoc, hc,mul_assoc]
 have he(i j)(h:i∈A)(p:j∈S): (F*V.val) i j= V.val i j:=by
    have hb:= Matrix.ext_iff.mpr hv i j; rw [cutM,Matrix.mul_diagonal,Matrix.mul_diagonal,if_pos p, mul_one,mul_one,cutM,Matrix.diagonal_mul,if_pos h,one_mul] at hb; exact hb
 constructor
 · unfold Reed.chemical; congr 1; apply sum_congr rfl; intro i h; congr 1; unfold Reed.tote; exact sum_congr rfl fun j p=>by rw [he i j h p]
 let s:= Fock.wedge V.val S; have hp:Sea P' C:= sea_g (D.plan _ u).1 _ p firstM; let c:=inner ℂ s C
 have hb:C=c • s:=by nth_rw 1 [← hp.1]; unfold P'; rw [H]; exact act_twistLine ..
 let x:=mateK N'; let b:=basisKet A; let d:= inner ℂ b x; have hs:Sea (cutM A) x:= (upper_q N') ▸ tickB N'; have hx:x=d • b:=by nth_rw 1 [←hs.1]; rw [cutLine, cut_oneAct]; unfold b d; rw [basis_inner]
 have hk:‖c‖=1:=by have he:=hp.2; rw [hb,norm_smul,show ‖s‖=1 from wedge_norm ..,mul_one] at he; exact he
 have hq :‖d‖=1:=by have ht:=hs.2; rw [hx,norm_smul,show ‖b‖=1 by simp [b,basisKet],mul_one] at ht; exact ht
 refine ⟨star d*c,(by rw [norm_mul,norm_star,hk,hq,one_mul]),fun X h=>?_⟩; rw [Reed.moment _ _ _ _ h]; change _=inner ℂ x (acts _ C); rw [hx,hb,map_smul,inner_smul_left,inner_smul_right,mul_assoc]; rfl
end YM.CF.Emu
