import YM.CF.Aroma.Tango
set_option autoImplicit false
noncomputable section
namespace YM.CF.Aroma
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Rush Cube MeasureTheory NormedSpace
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {n:Type*}[Fintype n][DecidableEq n]{N M:Side}
def why(N:Side):Momentum:=spark 1 (pinch N)
def vi(N:Side):ℂ:=cexpR (pinch N)
lemma hymn (x:Site (More N))(i:Axis): dialH (why N) (x+step i)=(if i=1 then vi N else 1)*dialH (why N) x:=by
 let F:Tide N (why N):=tide_pos 1; rw [← wrap_step, F.plusT]; have he :mode (why N) (step i)= if i=1 then vi N else 1:=by by_cases hx:i=1<;> simp [mode,vi,why,spark,hx,Ne.symm,cexpR,mul_comm] -- tune
 rw [he,mul_comm]
lemma tid1:Dir (amber (why N):Air N):=fun x i e=>by unfold amber; rw [hymn,if_neg e,one_mul] -- type
lemma tid2:Dir (zinnia (why N):Air N):=fun x i e=>by unfold zinnia; rw [hymn,if_neg e,one_mul]
lemma tint(J:InJ n N): (1-vi N) • firstH J (why N)= JD J (lop (amber (why N)))+Complex.I • JD J (lop (zinnia (why N))):=by
 let f:=JD J
 rw [stem_w,merit1 f _] -- tune
 rw [merit1 f (lop (zinnia _)), Finset.smul_sum, Finset.smul_sum,←sum_add_distrib]
 refine sum_congr rfl ?_; intro x hx; rw [lop, lop, amber,zinnia] -- tune
 simp only [amber,zinnia,hymn,ite_true]; let t:= dialH (why N) x
 change _ • _=((t.re-(vi N*t).re):ℝ) • f (spur x) + Complex.I • (((t.im-(vi N*t).im):ℝ) • f (spur x))
 rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),RCLike.real_smul_eq_coe_smul (K:=ℂ)]
 change (1-vi N) • t • _ = ((↑(t.re-(vi N*t).re):ℂ)) • f _+Complex.I • ((↑(t.im- (vi N*t).im):ℂ)) • f _
 rw [smul_smul,smul_smul,← add_smul, mul_comm Complex.I]; congr 1; rw [sub_mul,one_mul]; exact (Complex.re_add_im (t-vi N*t)).symm
lemma tune(T:Op n): ski T (amber (why N):Air N)+ Complex.I • ski T (zinnia (why N))= vi N • hub (tide_pos (N:=N) 1).σ fun _=> thrust T:=by
 let f:= (tide_pos (N:=N) 1); let c:= vi N; let V:Op (coneA n):=thrust T; let A i:= dialH (why N) (node (N:=N) i)
 have ht : ski T (amber (why N):Air N)+ Complex.I • ski T (zinnia (why N))=jump (Equiv.refl (Site N)) (fun i=> A i • V):=by unfold ski; rw [← jump_smul, ← jump_add]; congr 1; ext1 i; change ((A i).re:ℂ) • V + Complex.I • ((A i).im:ℂ) • V=A i • V; rw [smul_smul, mul_comm Complex.I,← add_smul,Complex.re_add_im]
 have hb (x:Site N): A x=mode (why N) (2 • natural x)*vi N:=by
    have he : node x=wrap (More N) (2 • natural x+1):=by
      unfold node; rw [map_add,Ratio.root_embed,show wrap _ (2 • _)=_ from Ratio.embed_wrap (assembly N) (natural x)|>.symm,nat_true]; congr 1; ext i; change (1: Per _) = ((1:ℤ): Per (More N)); simp
    have hz: mode (why N) (1:Cover)=vi N:=by simp [why,vi,mode,spark,cexpR,mul_comm]
    unfold A why; rw [he,f.money]; change mode (why N) _= mode (why N) _* _
    exact (mode_shift ..).trans (congrArg (_*·) hz)
 rw [ht,hubrate]; apply probe; intro x k i j; simp only [jump_apply, Equiv.refl_apply,ite_mul,zero_mul,sum_ite_eq, mem_univ,ite_true, Matrix.smul_apply,smul_eq_mul,Pi.smul_apply]; rw [hb, f.door]; unfold V why; ring
lemma growth {T:Op n}{j:ℕ}{J:InJ n N}(P:Foot T j M J)(w:16 ≤N.val):
 (1-vi N) • oak J (why N,minH N)=vi N •(thrust T* fuel n j M (minH N)-fuel n j M (minH N+spark 1 (2*(pinch N:ℂ)))*thrust T):=by
 let f:=tide_pos (N:=N) 1; let V:= fun _ : Site N=> thrust T; let P':= fun k :Site N=> fuel n j M (mel k)
 let z:=vi N
 have he: hub f.σ ((1-z) • fun k=>oak J (why N,mel k))=hub f.σ (fun i=> z • (V (f.σ i) *P' i-P' (f.σ i)*V i)):=by
   rw [← hubrate, ← oak_bind J P.smooth P.curve (why N) f]
   change (1-vi N) • firstH J (why N)= _; rw [tint,P.ride _ tid1,P.ride _ tid2]
   let a:= ski T (amber (why N):Air N); let b:=ski T (zinnia (why N):Air N); let Y:= J 0
   change a*Y-_ + Complex.I • (b*Y-_)=_
   rw [show a*Y-Y*a+Complex.I • (b*Y-Y*b)=(a+Complex.I • b)*Y+ -(Y*(a+Complex.I • b)) by simp only [add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul]; module]
   rw [show a+Complex.I • b= z • hub f.σ V from tune T,show Y=subHub P' from P.around,hubrate,lung,heart]; unfold hub; rw [←map_neg,← map_add,← jump_neg,← jump_add]; congr 2
   ext1 i; unfold V; simp only [Pi.add_apply, Equiv.apply_symm_apply,Pi.smul_apply,Matrix.smul_mul, Matrix.mul_smul, smul_sub]; abel -- tune
 have hp := congr_fun (hubfaith _ _ _ he) 0
 have hg:= (slid_f (n:=n) (why N) f (0:Site N) (trail8 1 1 w _ _ (by rw [abs_of_pos (pinch_pos _)])) j M).1
 rw [show minH N=mel (0:Site N) from riverB _,spark_plus]
 change _= z •(_-fuel n j M (spoon _ (why N))*_); rw [←hg]; exact hp
end YM.CF.Aroma
