import YM.CF.Pec.Ladle
import YM.Extra.ITERATION_NO_LOSS.Calibration
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pec
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}{α b:ℝ}
def oaks (P:Bed)(u v:Ps (More n)):ℝ := P.metric.acts _ (ŧ _ u) (ŧ _ v)
lemma row_dots {P:Bed}{p:RG.Clip}{C A η:ℝ}(h:Floor P p (More n) η C)(v:P.metric.strip α A)(t:0<α)(x:Orig n)(i j:PlaqAxes) : ∑ y: Orig n, oaks P (x,i) (y,j)= if i=j then 1 else 0:=by
 let T:= More n; let f:= P.metric (plaquette i) (plaquette j)
 have hz : (P.metric.read 0) (plaquette i) (plaquette j)=∑' x:Cover,(f x:ℂ):=by unfold Row.read; simp [Laurent.read]; rfl
 rw [h.starts,Matrix.one_apply,← Complex.ofReal_tsum] at hz
 have he(y:Orig n): Summable (fun z:Cover=> if y=x+wrap T z then f z else 0):=by have hh := (((v (plaquette i) (plaquette j)).unweighted t.le).2.1|> Summable.of_norm); exact (hh.indicator {z| y=x+wrap T z}).congr fun z=>by simp [Set.indicator,f]
 change (∑ y:Orig n, ∑' z:Cover, if y=x+wrap T z then f z else 0) = _ -- mistake
 rw [← Summable.tsum_finsetSum (s:=univ) (fun y _=> he y)]; simp_rw [Finset.sum_ite_eq',Finset.mem_univ,ite_true]; apply Complex.ofReal_injective; rw [←hz]; simp only [plaq_iff]; split <;> simp [ * ]
lemma oaksQ(P:Bed)(A:Cloud n): Bid.gaugeFiscal P A A = ∑ x:Ps (More n),∑ y: Ps (More n),oaks P x y*inner ℝ (heat (0:Orig n) (collect group A) (.inl x)) (heat (0:Orig n) (collect group A) (.inl y)) :=by
 rw [Iteration.Channel.fiscal_flux]; let K:=dColor group (More n) 1 A; let L:= P.metric.acts (More n); let V:= parts group 2 K
 have hp(j:group.ColorIndex): _= _:= (show Matrix.mulVec (d 1 (More n)) (parts group 1 A j)= V j from rfl)
 -- order of M* D tune
 simp_rw [Matrix.mulVec_mulVec, hp]; -- inspect
 let T (i:Body 2 (More n))(j:Body 2 (More n))(x:group.ColorIndex):=(V x i)* (L i j*(V x j)); simp_rw [← Matrix.mulVec_mulVec] -- rw under binder?
 change ∑ x:group.ColorIndex, (∑ i:Body 2 (More n),V x i* (∑ j:Body 2 (More n),L i j* V x j))= _; simp_rw [Finset.mul_sum]; rw [sum_comm]; unfold oaks; conv_lhs=> rw [← Equiv.sum_comp (ŧ (More n))]
 apply sum_congr rfl; intro i _; have he(i:Ps (More n)): heat 0 (collect group A) (.inl i)= K (ŧ _ i):= fundamental group ..
 conv_lhs=> rw [Finset.sum_comm]; rw [←Equiv.sum_comp (ŧ (More n)) (fun i=>_)] -- tune
 simp_rw [he]; refine sum_congr rfl ?_; intro k _; rw [Work.F03.inner_color,Finset.mul_sum]; apply sum_congr rfl; intro j _; unfold L V parts; ring
def bedV (P:Bed) (x:Site n)(i:Scan n):Dues n:=fun u v=>match u,v with
 | Sum.inl t, Sum.inl r=> if t.1=poolY x i then (16:ℝ)⁻¹ • (↑(oaks P t r):ℂ) else 0
 | _,_=>0
def rushP (P:Bed):Pride n:=fun x=>∑ i:Scan n,bedV P x i
def tasteA : Case:= fun i j=> if i=j then 1 else 0
lemma bed_r {P:Bed}{p:RG.Clip}{C A η:ℝ}(h:Floor P p (More n) η C)(v:P.metric.strip α A)(g:0<α)(x:Site n): mom (rushP P x)=tasteA:=by
 have he(t:Scan n)(i j:PlaqAxes): mom (bedV P x t) i j= (16:ℝ)⁻¹ • tasteA i j:=by
    unfold mom; rw [sum_eq_single (poolY x t)]; swap; intro k _ hx; simp [bedV,hx]; swap; simp
    simp_rw [bedV]; simp only [if_true, ←Finset.smul_sum, ←Complex.ofReal_sum]; rw [row_dots h v g]; split <;>simp [tasteA, *]
 funext i j; rw [show mom (rushP P x) i j=∑ v,mom (bedV P x v) i j from ?_]; swap; · unfold mom rushP; simp only [Finset.sum_apply]; rw [sum_comm (s:=(univ:Finset (Scan n)))]; refine sum_congr rfl fun i _=>?_ ; rw [sum_comm]
 simp_rw [he]; simp only [sum_const,card_univ,← Nat.cast_smul_eq_nsmul ℝ,smul_smul,show (↑(Fintype.card (Scan n)):ℝ)=16 from cardP n,mul_inv_cancel₀ (by norm_num:(16:ℝ)≠0),one_smul] -- tune
lemma octavo (P:Bed): WordK (n:=n) (rushP P):=by
 intro x y a b; simp_rw [rushP,Finset.sum_apply]; apply sum_congr rfl; intro k _; set T:= assembly n
 have he(i: Orig n)(p:PlaqAxes):feedback y (Sum.inl (i,p))= Sum.inl (i+T.embed y,p):=by change Sum.inl (i+wrap _ (2 • lift y),p) = _; rw [←show T.embed (wrap _ (lift y))=wrap _ (2 • lift y) from Ratio.embed_wrap ..,wrap_lift]
 cases a with
 | inl i=> cases b with
   | inl j=> rcases i with ⟨x',p⟩; rcases j with ⟨y',q⟩; rw [he,he]; unfold bedV; rw [rosemary]; dsimp only; by_cases h:x'=poolY x k; swap; · rw [if_neg h,if_neg (fun p=> h (add_right_cancel p))]
             rw [if_pos h,if_pos (congrArg (· +T.embed y) h)]; unfold oaks Row.acts; congr 3
             simp [ŧ,add_right_comm x' (T.embed y)]
   | inr j=> rfl
 | inr i=> cases b <;> rfl
end YM.CF.Pec
