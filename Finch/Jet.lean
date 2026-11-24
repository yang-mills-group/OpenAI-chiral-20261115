import Finch.MatrixMark
import Zephyr.Bed

/-! The affine test taken on first-pane links, on the MASKED stencil itself. -/

set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill Buffered StressExchange Window
open _root_.Zephyr.Chern
variable {N:Side}{P:SOp N}{o:Seat N}{a b c d v B:ℝ}{p:BudgetPoint}{k r:ℕ}{A:Scree.Loom N}{O:Site N}

def profileJet (P:SOp N)(L:StemA N)(t:ℝ):ℂ:= Matrix.trace (P (profile (petals L t)))
lemma petalsPass (A:Scree.Loom N)(p:BudgetPoint)(o:Seat N)(P:SOp N)
    (h:Roof N b d r A)(f:p.threshold≤ b)(L:StemA N):
    (fun t=>markMatrix A p o P (petals L t))=ᶠ[𝓝 0] (fun t=> P (profile (petals L t))) := by
 have hz: Tendsto (petals L) (𝓝 0) (𝓝 1):=by simpa only [petal_idle] using (cont_petal L).tendsto 0
 filter_upwards [hz.eventually ((ping_o (e:=p.threshold) (X:=univ)).mem_nhds (ping_f p univ))] with t u
 change pingS p.threshold univ (petals L t) at u
 have hv: pingS b univ (petals L t):=fun i v=>(u i v).trans_le f
 unfold markMatrix; rw [Set.indicator_of_mem (show pingS p.threshold _ _ from fun i m=> u i (fun v=>m (Disjoint.mono_left (subset_univ _) v))), show A (petals L t,Classical.arbitrary _)=petals L t from ?_]
 funext i; exact h.lamp _ _ _ (Disjoint.mono_right (subset_univ _) (ping_le hv).symm)

-- exponential estimate for whole trace, paying W ONCE not per mode
lemma traced_jet (L:StemA N) (Θ:Oily a d B c) (Y:Temper o L B) (X:Soak o P a v d) :
    Bud (profileJet P L) ∧ ∀ n:Fin 3, ‖bud (profileJet P L) n‖ ≤ c*v:=by
 obtain ⟨F,C,p,t,q,g⟩:=X
 let Z (S:Sa N)(x:Chin N) := if h:x ∈ Openc (More N) d then F S ⟨x,h⟩ else 0
 have hz(S:Sa N):Piece d S (C S) (Z S):=by
    have T:F S=fun x=>Z S x.val:=funext fun x=>by simp [Z,x.property]
    have k:=p S; rw [T] at k; exact k
 let π (i:Single N)(S:Sa N):=_root_.Zephyr.Chern.wad (Z S) L i i
 have hl: Bloom (profileJet P L) (∑ i:Single N, ∑ S:Sa N,π i S):=by
    have he(i:Single N)(S:Sa N): Bloom (drip (Z S) L i i) (π i S):=(kernel_bud (hz S) Θ.s.ready).bloom
    refine (Bloom.sum univ fun i _=> Bloom.sum univ (fun S _=> he i S)).congr ?_
    filter_upwards [petals_open Θ.s.ready L] with t hx; let U:Openc (More N) d:=⟨profile (petals L t),hx⟩
    change Matrix.trace (P U.val)=_; rw [g U]; unfold Matrix.trace Matrix.diag; simp only [Matrix.sum_apply]; unfold drip; simp [Z,hx,U]
 have hv(i:Single N)(S:Sa N)(n:Fin 3) : ‖π i S n‖ ≤ c* (rent a S * C S i i):=by
    by_cases p:C S i i=0; · simp [π,wad,(kernel_free (hz S) p Θ.s.ready L).bud_eq,p]
    have hm:o∈S:=Classical.not_not.mp (fun w=>p (by rw [t S w]; rfl))
    have w:= ((hz S).expo i i).triggered p
    have e:∀ x∈leaks S,|L x|≤ B*(1+(S.card:ℝ)):= fun x hx=>(Y.grow x).trans (mul_le_mul_of_nonneg_left (add_le_add_right (by exact_mod_cast (w.1.lim x.1 (mem_filter.mp hx).2.1 o hm).le) _) (zero_le_one.trans Y.above))
    refine ((kernel_jet (hz S) Θ.s (one_le_mul_of_one_le_of_one_le Y.above (by simp)) e).2 n).trans ?_; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ ((hz S).nonn _ _); refine (Θ.q S.card).trans ?_
    apply mul_le_mul_of_nonneg_left _ Θ.bound.le; exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (half_le_self Θ.hb.le) (Nat.cast_nonneg _))
 refine ⟨hl.1, fun n=>?_⟩; rw [hl.bud_eq]; simp_rw [Finset.sum_apply]; rw [sum_comm]; refine ( (norm_sum_le ..).trans (sum_le_sum fun i _=>(norm_sum_le ..).trans (sum_le_sum fun j _=>hv j i n))).trans (le_trans ?_ (mul_le_mul_of_nonneg_left q Θ.bound.le)); rw [mul_sum]; apply sum_le_sum; intro i _; rw [←mul_sum, ←mul_sum]; apply mul_le_mul_of_nonneg_left _ Θ.bound.le; apply mul_le_mul_of_nonneg_left _ (rent_pos _ _).le; exact sum_le_sum fun j _=>single_le_sum (fun k _=> (hz i).nonn j k) (mem_univ j)

lemma actualJet (L:StemA N) (Θ:Oily a d B c) (h:Roof N b d r A)(X:Soak (node O) P a v d)
    {U W:SOp N} {g:ℝ}(t:Soak (node O) U a g d)(Y:Temper (node O) L B)(ℓ:p.threshold ≤ b)
    (T:∀ V:Openc (More N) d,W V.val=P V.val+U V.val):
    Bud (inkCost A p O P ∘ petals L) ∧ Bud (profileJet W L) ∧ ∀ n:Fin 3, ‖bud (profileJet W L) n-bud (inkCost A p O P ∘ petals L) n‖ ≤ c*g:=by
 let w:=traced_jet L Θ Y X; let v':=traced_jet L Θ Y t
 have ht : inkCost A p O P ∘ petals L=ᶠ[𝓝 0] profileJet P L:= (petalsPass A p _ P h ℓ L).mono fun i u=>congrArg Matrix.trace u
 have hz: profileJet W L=ᶠ[𝓝 0] (fun x=> profileJet P L x+profileJet U L x):= by
    filter_upwards [petals_open Θ.s.ready L] with i y; unfold profileJet; rw [T (⟨_,y⟩:↥(Openc (More N) d)),Matrix.trace_add]
 let H:= (w.1.bloom.add v'.1.bloom).congr hz
 refine ⟨(w.1.bloom.congr ht).1,H.1,fun n=> ?_⟩
 rw [H.bud_eq,bud_congr ht,Pi.add_apply,add_sub_cancel_left]; exact v'.2 n

-- lifts of fixed Stride as momentum flux tests. Matrix trace identity on EVERY period.
lemma perSite_identity (M:Op (Single N))(x:Site N) : Matrix.trace (M*millQ x)=∑ i:IS,M ((x,i.1),i.2) ((x,i.1),i.2):=by
 rw [millSt,Tye.stock]; simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_diagonal]
 -- split product sums (fintype)
 change (∑ i:(Site N × SpinIdx)×SU.Slot, M i i * (if node i.1.1=node x then 1 else 0))=_
 simp [Fintype.sum_prod_type_right,unaryN.eq_iff] -- tune

open Py.Rate LocalLimit Preparation
open Buffered.Afterglow.Tower.VacuumSelection
variable (P:Spine)
def jetAt (R:Side)(S:SOp R)(L:StemA R)(x: Site R)(m:ℕ)(U:List Axis):= profileJet (fun y=>(S y-tickA R)* squareSum millQ m U x) L
lemma jetEach (X: _root_.Zephyr.Chern.SprigFee P) (x:Cover)(m:ℕ) : ∃ c> (0:ℝ), ∀ᶠ s in atTop,∀ i k,
    let N:= age P.run i s; let F:= funde P.par.K.j (blood P.run i k s) N; let U:= jetAt N F (stream N) (wrap N x) m []
    Bud U ∧ c<(bud U 2).re:=by
 obtain ⟨δ,v,q⟩:=X.actual x; refine ⟨δ,v,q.mono fun s p i k=>?_⟩; let N:=age P.run i s; let M:= blood P.run i k s; let F:= funde P.par.K.j M N; let U:=jetAt N F (stream N) (wrap N x) m []
 let S:=millQ (wrap N x); let z:ℂ:= -Matrix.trace (tickA N*S)
 have t: U=sparSite (N:=N) P.par.K.j M x+Function.const _ z :=by
    funext t; change Matrix.trace ((_ - _)*millQ _)= (∑ i:IS,_)+(-Matrix.trace _); rw [sub_mul,Matrix.trace_sub,perSite_identity]; rfl
 change Bud U∧ δ< (bud U 2).re; rw [t]; exact p i k z

lemma jetLots (X:_root_.Zephyr.Chern.SprigFee P) (x:Cover) (m:ℕ)(u:1 ≤ m)(U:List Axis) : ∃ c> (0:ℝ), ∀ᶠ s in atTop,∀ i k,
    let N:= age P.run i s; let F:= funde P.par.K.j (blood P.run i k s) N; let Z:= jetAt N F (stream N) (wrap N x) m U
    Bud Z ∧ c<(bud Z 2).re:=by
 induction U generalizing x with
 | nil=> exact jetEach P X x m
 | cons a U h=>
    let z(i:ℕ): Cover:= x-m • step a+(i+1) • step a
    choose c v f using fun i:ℕ=>h (z i)
    let S:= Finset.range (2*m); let E:0∈ S:=mem_range.mpr (by omega); refine ⟨c 0,v 0,?_⟩
    filter_upwards [(Filter.eventually_all_finset S).mpr (fun i _=> f i)] with s q i k
    let N:=age P.run i s; let F:=funde P.par.K.j (blood P.run i k s) N; let G:=jetAt N F (stream N); let M(j):= G (wrap N (z j)) m U
    let g:= G (wrap N x) m (a::U)
    have hp:g = fun x=>∑ j∈S,M j x:=by
       funext y; change Matrix.trace ((_ - _)* (∑ j∈S, _))=_; rw [mul_sum,Matrix.trace_sum]; refine sum_congr rfl fun j v=>?_
       unfold M G jetAt profileJet z; rw [map_add,map_sub,map_nsmul,map_nsmul,wrap_step]
    have H(j)(t:j∈S) : Bud (M j) ∧ c j<(bud (M j) 2).re:=q j t i k
    have ht: Bloom g (∑ j∈ S, bud (M j)):= by rw [hp]; exact Bloom.sum S (fun i t=>(H i t).1.bloom)
    refine ⟨ht.1,?_⟩; change c 0<(bud g 2).re; rw [ht.bud_eq,Finset.sum_apply,Complex.re_sum]; exact (H 0 E).2.trans_le (single_le_sum (fun i v'=>((v i).trans (H i v').2).le) E)
-- compare unprojected (or changed projections later)
end YM.CF.Swell
