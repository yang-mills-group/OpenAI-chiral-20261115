import YM.CF.Dial.Value
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
-- reindex patch columns
abbrev Hand := Site N × Site G.count
def abbe : Iota G ≃ Hand G × QuiltF:= ((Equiv.prodAssoc ..).symm.prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc ..)
lemma abbe_at (a:Hand G× QuiltF): abbe G ((a.1.1,a.1.2,a.2.1),a.2.2)=a:=rfl
def readK (A: Hand G→Op QuiltF) : Op (Iota G):= (jump (Equiv.refl _) A).submatrix (abbe G) (abbe G)
lemma readK_mul(A B): readK G A*readK G B=readK G (A*B):=by unfold readK; rw [Matrix.submatrix_mul_equiv,jump_mul]; rfl
lemma readK_star(A):star (readK G A)= readK G (star A):=by change (star (jump (Equiv.refl _) A)).submatrix (abbe G) (abbe G)=_; rw [jump_star]; rfl -- tune
lemma readK_cc(A):cc (readK G A)=readK G (fun i=>cc (A i)):=by change (cc (jump (Equiv.refl _) A)).submatrix (abbe G) (abbe G)=_; rw [jump_cc]; rfl
lemma readK_one:readK G 1=1:=by rw [readK,show jump (Equiv.refl (Hand G)) (1:Hand G→Op _)=1 from jump_id]; ext; simp [Matrix.one_apply]
def tableD(u:Bool)(x:Bale N P): Hand G →Op QuiltF:= fun i=> if u then x.2.1 (node (isle G (i.1,i.2))) true else x.2.2 (node i.1) true
def squareD(u:Bool)(x:Bale N P):=readK G (tableD G u x)
lemma unit_table (u:Bool)(x:Sew N P)(i:Hand G): tableD G u (post x) i ∈unitary (Op QuiltF):=by cases u<;> exact localPair_mem _ (hookN ..)
lemma table_skew (u:Bool)(x:Sew N P)(i:Hand G): (tableD G u (post x) i)ᵀ= -tableD G u (post x) i:=by cases u <;> exact localPair_skew _ (hookN ..)
lemma unit_square (u:Bool)(x:Sew N P): squareD G u (post x)∈unitary (Op (Iota G)):=by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  change star (readK G _) * _=_; rw [squareD,readK_star,readK_mul,←readK_one]; congr 1; funext i; exact (unit_table G u x _).1
lemma skew_square (u:Bool)(x:Sew N P): (squareD G u (post x))ᵀ= -squareD G u (post x):=by
  ext i j; unfold squareD readK; by_cases h:(abbe G i).1=(abbe G j).1
  · simp only [Matrix.transpose_apply,Matrix.submatrix_apply, Matrix.neg_apply, jump_apply, Equiv.refl_apply,h,ite_true]; exact Matrix.ext_iff.mpr (table_skew G u x _) _ _
  simp [Matrix.transpose_apply,jump_apply, h,Ne.symm h]

def harborT(g:Site (More P)→E)(u:Bool): Hand G→UNI QuiltF:= fun i=>coinK (g (touch G u (i.1,i.2,0)))
lemma hatch(g:Site (More P)→E)(u:Bool)(e:ℝ): ((rod G u e).run g).val=readK G (fun i=>(harborT G g u i).val):=by
  rw [rod]; change ((Peaks.parcel ..).run g).val=_; rw [warrant]
  ext ⟨⟨i,a,b⟩,l⟩ ⟨⟨j,c,d⟩,m⟩; simp only [readK,Matrix.submatrix_apply, jump_apply, Equiv.refl_apply]; rw [show abbe G ((i,a,b),l)=((i,a),b,l) from rfl,show abbe G ((j,c,d),m)=((j,c),d,m) from rfl]; by_cases h:(i=j ∧ a=c) <;> by_cases g':b=d <;> cases u <;> simp [h,and_assoc.symm,g',harborT,coinK, Lat.color, Matrix.one_apply] <;> try rfl -- h.1 only pos
lemma table_int (u:Bool)(e): Inter (rope G (u,true) e) (rope G (u,false) e) (fun x=>squareD G u x.val):=by
  intro g x; let V:=((rod G u e).run g).val; let S:=rope G (u,false) e; let T:= harborT G g u
  have hg := hatch G g u e
  change squareD G u (novel G g x.val)*cc V= V*squareD G u x.val; unfold V; rw [hg]; unfold squareD; rw [readK_cc, readK_mul, readK_mul]
  congr 1; funext i; let K:= (T i).val; let W:=cc K; let Y:=tableD G u x.val i
  have he :tableD G u (novel G g x.val) i = K*Y*star W:=by cases u <;> rfl
  simp only [Pi.mul_apply,he]; change _*W=K*Y; rw [mul_assoc,show star W*W=1 from (ccU (T i)).property.1,mul_one]
end YM.CF.Dial
