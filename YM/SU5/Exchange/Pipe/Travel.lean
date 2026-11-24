import YM.SU5.Exchange.Pipe.Center
import YM.CF.Sour.Vill
import YM.CF.Tye.Spin
import YM.CF.Song.Loom
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}
local notation "Ω"=> Single N
-- conductor.front matter shift. not just Sector2. natural signs earns only b=false
abbrev taxiPlus(t:Site N): Sweep N:=⟨1,t,false⟩
lemma platforms(t x:Site N): boxA (taxiPlus t) (node x)=node (x+t):=by
 rw [sitA]; unfold affine node; change (Signed.act 1 _)+ (assembly N).root t=(assembly N).root (x+t)+1
 rw [Signed.act_one,map_add]; change (assembly N).root x+1+_= _; abel
lemma unaryN:Injective (node (N:=N)):=fun x y h=> (assembly N).embed_injective (add_right_cancel h)
lemma millSt(x:Site N): millQ x=Tye.stock (node x):=by
 ext ⟨⟨y,i⟩,b⟩ ⟨⟨z,j⟩,c⟩
 have hs: Font.place_x ((y,i),b)=node y:=rfl
 unfold Tye.stock; by_cases k:y=x<;> by_cases p:z=x<;> by_cases v:i=j<;> by_cases w:b=c <;> simp [millQ,place_x,Matrix.diagonal_apply, Matrix.sum_apply,Tulip.panel,Matrix.one_apply, *,ite_and,Ne.symm,unaryN.eq_iff] -- tune pace
lemma millMotion (t x:Site N): ech (taxiPlus t) (millQ (x+t))= millQ x:=by rw [millSt,millSt,← platforms]; exact Tye.proM (boxA _) (boxA _).injective false (γS (taxiPlus t)) (fun i j h=> Tye.birth_l i j _ _ _ h) _ -- tune implicit
-- posture actual.Arte.
variable (V:Pane N)(t:Site N)
local notation "Xν"=> taxiPlus t
local notation "X'"=> flashA Xν V
local notation "L"=> fun F:Op Ω=>ech Xν F
lemma chuteMotion (O:Site N→ SOp N)(p:∀ x,L (O (x+t) (profile V))=O x (profile X'))(x:Site N)(a:Axis) : L (chute O (x+t) a (profile V))= chute O x a (profile X'):=by
 let H:= twist (γS Xν); have ht : ech Xν=H:=rfl
 let Q(i j:Site N):= mural O i j (x+t) a (profile V)
 have hp(i j): H (Q (i+t) (j+t))=mural O i j x a (profile X'):=by
    let U:=mural O (i+t) (j+t) (x+t) a; unfold Q mural; rw [pipeStep, show (H) ((_:ℂ) • (O (i+t) _*millQ (j+t))) = _ from (twist_scalar (γS Xν) _ _), map_mul] -- tune
    rw [show twist (γS Xν) (O (i+t) (profile V))= O i (profile X') from p i,show twist (γS Xν) (millQ (j+t))=millQ j from millMotion t j]
 change ech Xν (∑ i,∑ j,Q i j)=_
 rw [ht,map_sum]
 let T:= Equiv.addRight t; unfold chute; rw [←Equiv.sum_comp T]; apply sum_congr rfl; intro i _; rw [map_sum,←Equiv.sum_comp T]; apply sum_congr rfl; intro j _; exact hp i j
lemma spurMotion(O:Site N→ SOp N)(p:∀ x,L (O (x+t) (profile V))=O x (profile X'))(x:Site N)(a:Axis)(m:ℕ) : L (spur O (x+t) a m (profile V))= spur O x a m (profile X'):=by
 let f: Op Ω→+ Op Ω:=(twist (γS Xν)).toRingEquiv.toRingHom.toAddMonoidHom -- tune
 unfold spur; rw [←square_move _ t]; rw [show L _= _ from (squareMap f _ m _ _)]; congr! 2; rename_i i; exact chuteMotion V t O p i _ -- tune

variable {P K: SOp N}
structure Staffer (P K : SOp N)(d:ℝ):Prop where
  projection(V:Pane N): Guard V d→IsStarProjection (P (profile V))
  passport(t: Site N)(V:Pane N): Guard V d→ P (profile (flashA (taxiPlus t) V))=ech (taxiPlus t) (P (profile V))
  envoy(t:Site N)(V:Pane N): Guard V d→ K (profile (flashA (taxiPlus t) V))=ech (taxiPlus t) (K (profile V))
-- derive from same P supplies in next file
abbrev millIntro (P K: SOp N)(x:Site N)(V:Chin N):= Sault.inward (P V) (millQ x) (K V)
lemma millIntro_moves(f:Staffer P K d)(p: Guard V d) (x:Site N) : (Xν).charge=false ∧ L (millIntro P K (x+t) (profile V))=millIntro P K x (profile X'):=by
 refine ⟨rfl,?_⟩; unfold millIntro inward; rw [f.passport _ _ p,f.envoy _ _ p]; let H:=twist (γS Xν); let X:=P (profile V); let S:=K (profile V); let M:=millQ (x+t); change H (inward X M S)=inward (H X) _ (H S)
 unfold inward blockD Kennel.capT; simp only [map_add,map_sub,map_mul,map_one]; rw [show H M=millQ x from millMotion ..]; -- tune
lemma limb (p:Staffer P K d)(x:Site N)(a:Axis)(g:Guard V d)(m:ℕ): L (spur (millIntro P K) (x+t) a m (profile V))=spur (millIntro P K) x a m (profile X'):= spurMotion _ _ _ (fun _=>(millIntro_moves V t p g _).2) _ _ _
end YM.CF.Swell
