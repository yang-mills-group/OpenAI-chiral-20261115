import YM.SU5.Diva.Spiro
import YM.SU5.Hiro.Crisp
import YM.SU5.WakeInvestment.Richly

/-! # The *raw* IA.4 appointment, orientation and lift prices.
Keep weighting convention paid before comparing. `R=(R:ℕ)` scale in this file in MATTER mesh;
physical r=(2R)*h_s; the actual scaled-cost call with real $R_s$ can use a slightly different
argument. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Ballad.SitSpin
open Function Filter Fock Finset Cube Spire Scroll MeasureTheory Skye Pastry Phase Scree RG Branch RP Reflect Wilson Lat Rush SU Lat Lattice Peaks Tulip Afterglow Heat Advance Vale Window
open Reed (Fine)
open Lamour.Bridge.Celeste
open Py.Rate.LocalLimit.Papal
open WakeInvestment
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder ContDiff
attribute [local instance] opCStarAlgebra
open Lifted
open Lead (Clan)
variable {N:Side} (U:Lead.Clan)(u:Cover)

def raw (s:Cover)(U:Clan)(a b: Fin 2): Weaver:= fun N _=> ∑ i ∈ colors U, Fock.create (basisC N s (upSpin a) i)* Fock.remove (basisC N s (dnSpin b) i)
abbrev qRaw := (1/16:ℂ) • raw u U 0 0
lemma printed (N:Side)(x:Fields N): qRaw U u N x=(1/16:ℂ) • ∑ i∈colors U,Fock.create (basisC N u 0 i)* Fock.remove (basisC N u 2 i):=rfl -- order of arguments section?
lemma print_family (K:Calibration):household K (qRaw U u)=(1/16:ℂ) • ∑ i∈colors U,creation K u 0 i * removal K u 2 i:=by
 funext m x; change qRaw U u _ x=_; rw [printed]; simp only [Pi.smul_apply, Finset.sum_apply,Pi.mul_apply,creation,removal]
lemma cr_swap {N:Side}(a b v u)(i j:SU.Slot) : Fock.remove (basisC N u (dnSpin b) i)*create (basisC N v (upSpin a) j)= -(create (basisC N v (upSpin a) j)*Fock.remove (basisC N u (dnSpin b) i)):=by
 unfold basisC Fock.remove; simp only [map_smul,create_put,star_smul,Matrix.smul_mul,Matrix.mul_smul]
 have he:Lifted.index N u (dnSpin b) i≠ Lifted.index N v (upSpin a) j:=fun h=> dn_half b ((show dnSpin b=upSpin a from congrArg (fun t:Single N=> t.1.2) h).symm ▸ up_half a)
 rw [show star (put _)*put _= _ from eq_neg_of_add_eq_zero_left ((mixed _ _).trans (if_neg he)),smul_neg,smul_neg,smul_comm]
lemma in_Twah (R:ℕ)(a b:Fin 2) : (Hiro.unifyT u (a,b)).groundWord R U=(R:ℂ)^3 • raw u U a b:=by
 funext N x; let A:=Hiro.unifyT u (a,b); have ht:A.laps (N:=N) x.1=1:=rfl
 unfold raw Twah.groundWord; change Twah.gold R • (∑ p∈ colors U,∑ q∈colors U,A.coil x.1 p q • (Fock.remove (A.lower N q) * create (A.upper N p))) = (R:ℂ)^3 • _
 simp_rw [Twah.coil,ht, map_one]; rw [smul_sum,smul_sum]; apply sum_congr rfl; intro i v; rw [Finset.sum_eq_single_of_mem i v]; swap; · intro j h p; rw [show ((1:UNI SU.Slot).val i j)=0 from Matrix.one_apply_ne (Ne.symm p),zero_smul]
 rw [show ((1:UNI SU.Slot).val i i)=1 from Matrix.one_apply_eq i, one_smul]; change -(R:ℂ)^3 • (Fock.remove (basisC N u (dnSpin b) i) * create (basisC N u (upSpin a) i))= _; rw [cr_swap]; exact neg_smul_neg _ _

lemma voice (a b:Fin 2): Voice (raw u U a b) {nodeC u}:=by have hx:=Gemini.flourish (Hiro.unifyT u (a,b)) U (R:=1); rw [in_Twah] at hx; simpa [Twah.patio,Hiro.unifyT, visits] using hx
lemma qVoice : Voice (qRaw U u) {nodeC u} := (voice U u 0 0).hushed _
lemma qLink (N:Side)(x y:Fields N) : qRaw U u N x=qRaw U u N y:=rfl

section
lemma basisRent (N:Side)(u:Cover)(i:SpinIdx)(p:SU.Slot): ‖basisC N u i p‖=1 ∧ withinM (modesIn N (dBook N {nodeC u})) (basisC N u i p):=by
 constructor; · unfold basisC Lifted.winding; rw [norm_smul,Rush.fee_norm]; simp
 unfold withinM basisC; rw [map_smul,within_basis _ (Lifted.index N u i p)]; rw [modes_at]; change node (wrap N u)∈ dBook N {nodeC u}; rw [node_of]; exact mem_image_of_mem _ (mem_singleton_self _)
lemma cadre (N:Side)(a b:Fin 2)(x:Fields N) : Cadre (modesIn N (dBook N {nodeC u})) 2 (Fintype.card SU.Slot:ℝ) (raw u U a b N x):=by
 let W(i:SU.Slot)(j:SpinIdx)(b:Bool):= Cadre.leaf b (basisC N u j i) (basisRent N u j i).2 (basisRent N u j i|>.1.le)
 unfold raw; apply (Cadre.sumF (colors U) (fun i (_:i∈ colors U)=> Cadre.and_ (W i (upSpin a) false) (W i (dnSpin b) true))).buy (by decide)
 simp only [sum_const,nsmul_eq_mul,mul_one]; exact_mod_cast (card_le_univ (colors U))

-- keep cost dictionary relative to movement. 
variable {I:Type*}(g:I→Clan)(a:I→ Cover)(b:I→Twah.DirSpin) (R:ℕ)(L:List I)
abbrev rest(i:I):Twah:= Hiro.unifyT (a i) (b i)
def lay (a:I→ Cover)(L:List I): Finset Cover:= (L.map (fun i=> nodeC (a i))).toFinset
abbrev reader:= Twah.plait (rest a b) g L R
abbrev factor (R:ℕ) :ℝ:= R^3 * (Fintype.card SU.Slot:ℝ)
lemma put_patio : Twah.paper (L.map (rest a b))= lay a L:=by
 induction L with|nil=> simp [lay,Twah.paper]|cons i L ih=> change Twah.patio (rest a b i) ∪ Twah.paper (L.map (rest a b)) = _; rw [ih, show rest a b i=Hiro.unifyT (a i) (b i) from rfl,show lay a (i::L)=insert (nodeC (a i)) (lay a L) from List.toFinset_cons]; simp [Twah.patio,Lattice.visits]
lemma reader_voice : Voice (reader g a b R L) (lay a L):= put_patio a b L ▸ Twah.lovely (rest a b) g L R -- order arguments uses declared section vars
lemma reader_price(N:Side)(x:Fields N): Cadre (modesIn N (dBook N (lay a L))) (2*L.length) ((factor R)^L.length) (reader g a b R L N x):=by
 induction L with
 | nil=> simpa [reader,Twah.plait] using (Cadre.unit (s:=modesIn N (dBook N (lay a []))))
 | cons i L ih=>
    let F:= raw (a i) (g i) (b i).1 (b i).2; let S:=lay a (i::L); have he:S= {nodeC (a i)}∪ lay a L:=by unfold S lay; simp
    let V:=(R:ℂ)^3
    have hv:‖V‖=(R:ℝ)^3:=by simp [V]
    have ht:Cadre (modesIn N (dBook N (lay a (i::L)))) (2+2*L.length) (factor R*(factor R)^L.length) (V • (F N x)* reader g a b R L N x):=by
       change Cadre (modesIn N (dBook N S)) _ _ _; rw [he]; have h: factor R=‖V‖*(Fintype.card SU.Slot:ℝ):=by rw [hv]
       apply Cadre.and_ _ (ih.cover (modes_monotone (Finset.image_subset_image subset_union_right))); rw [h]; exact (((cadre (g i) (a i) N _ _ x).scale V).cover (modes_monotone (Finset.image_subset_image subset_union_left)))
    rw [List.length_cons,pow_succ',Nat.mul_succ,add_comm (2*L.length)]; let Q:=Twah.plait (rest a b) g L R; change Cadre _ _ _ (((rest a b i).groundWord R (g i) N x)*Q N x);
    have heq: (rest a b i).groundWord R (g i)=V • F:= in_Twah ..; rw [heq]; exact ht
lemma reader_link (N:Side)(x y:Fields N): reader g a b R L N x=reader g a b R L N y:=by
 induction L with|nil=> rfl|cons i L ih=> change (rest a b i).groundWord R (g i) N x * reader g a b R L N x= (rest a b i).groundWord R (g i) N y* reader g a b R L N y; rw [ih]; rfl
end

open Mir
-- Theta3 of status 00. Actual calibration including both windings, parity order.
private lemma spin_00 (j: SpinIdx) : pin 3 j 0=(if j=(2:SpinIdx) then 1 else 0) ∧ pin 3 j 2=(if j=0 then -1 else 0):=by
 fin_cases j
 · simp only [pin,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ,Fintype.sum_empty] 
   change ((0*(1)+ (0*(0) + (1*(0) + (0*(0) + 0)))) :ℂ)=0 ∧ ((0*(0)+ (0*(0) + (1*(-1) + (0*(0) + 0)))) :ℂ)= -1; norm_num
 · simp only [pin,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ,Fintype.sum_empty] 
   change ((0*(1)+ (0*(0) + (0*(0) + (1*(0) + 0)))) :ℂ)=0 ∧ ((0*(0)+ (0*(0) + (0*(-1) + (1*(0) + 0)))) :ℂ)=0; norm_num
 · simp only [pin,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ,Fintype.sum_empty] 
   change ((1*(1)+ (0*(0) + (0*(0) + (0*(0) + 0)))) :ℂ)=1 ∧ ((1*(0)+ (0*(0) + (0*(-1) + (0*(0) + 0)))) :ℂ)=0; norm_num
 · simp only [pin,Matrix.mul_apply,SpinIdx,Fin.sum_univ_succ,Fintype.sum_empty] 
   change ((0*(1)+ (1*(0) + (0*(0) + (0*(0) + 0)))) :ℂ)=0 ∧ ((0*(0)+ (1*(0) + (0*(-1) + (0*(0) + 0)))) :ℂ)=0; norm_num
lemma q_reflect (N:Side)(s:ℤ): reflMark (n:=N) 3 s (qRaw U u N)= qRaw U ((plane 3 s).flee u) N:=by
 funext X; unfold reflMark; rw [printed,printed,theta_smul, theta_sum, show star (1/16:ℂ)= 1/16 by norm_num]; refine congrArg ((1/16:ℂ) • ·) (sum_congr rfl fun i _=>?_); let v:= (plane 3 s).flee u; let f:= basisC N v 2 i; let g:=basisC N v 0 i
 rw [theta_mul, (Lifted.flips_basisC 3 s N u 0 i).1,(Lifted.flips_basisC 3 s N u 2 i).2]
 simp_rw [(spin_00 _).1,(spin_00 _).2,ite_smul,zero_smul,sum_ite_eq',mem_univ,ite_true,one_smul,neg_one_smul]
 rw [map_neg]; change (-Complex.I • Fock.remove f)*(Complex.I • -create g)= _;
 have h: Fock.remove f * create g= -(create g * Fock.remove f):=cr_swap 0 0 v v i i;
 rw [smul_neg, mul_neg,Matrix.smul_mul,Matrix.mul_smul,smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul,h, neg_neg]; try rfl
#print axioms q_reflect

set_option pp.universes false in
#print axioms reader_price
#print axioms print_family
end YM.CF.Buffered.Ballad.SitSpin
