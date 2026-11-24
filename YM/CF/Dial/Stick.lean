import YM.CF.Dial.Paint
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
variable {ι:Type*}{L:Side}{u v:AxisT}{A B:Chop ι}{a r e s c:ℝ}{k:ℕ}
omit G
lemma anchor_dusk (p:IndexB L u v A a r e k)(c:ℝ)(h:0≤c)(H:∀ i {N P : Side}(G: Ratio N P),G.count=L→ k≤N.val→ ‖A i G (vacancyY N P)‖ ≤ c)(he:0<e)
    (n:ℕ)(d:ℝ)(w:ℝ)(hw:0<w)(g:w≤1)(hb:0<d)(hx:d≤a/2):∃ m:ℝ,0<m∧m≤e∧∃ t:ℕ,
    IndexB L u v A d (let U:=quota*(((↑(n+n):ℝ)+1)^4); let T:= Real.exp (-a/2*n)*r; U*Real.exp (d*U)*(c+T+r*(w+w))+T) m t :=by
  obtain ⟨b,ht,V⟩:=sluice (n+n) L (w*e) (mul_pos hw he)
  let m:=min b (w*e); have hm :0<m:= lt_min ht (mul_pos hw he)
  have hQ:m ≤ w*e:=min_le_right ..; have hy:m≤e:=hQ.trans ((mul_le_mul_of_nonneg_right g he.le).trans (le_of_eq (one_mul _)))
  refine ⟨m,hm,hy,k + (2*(n+n+L.val)+3),fun i N P G hv hg=>?_⟩
  let f:TopK G m→ TopK G e:=fun x=>⟨x.val,portland G x.property hy⟩
  let X:TopK G e:=⟨vacancyY N P,vacant G _ he⟩
  let hP:0≤a:=by linarith
  have hY:=crewD G hm hy hQ
  have hl:k ≤ N.val:=by omega
  have hc:0≤quota:=(by norm_num:(0:ℝ)≤16) |>.trans quota_bound
  obtain ⟨F,C,hf,q,W⟩:= p i G hv hl
  have hB:= (H i G hv hl); have hA:= hY.dusk (s':=rope G u m) (t':=rope G v m) (A:=fun x=> A i G x.val) F C hf q (cD G _) hc hP X n (W X) g (ropes G u _ _) (ropes G v _ _) w hw.le c h hB ?_ hb.le  -- def eq
  · simp only [abs_of_pos hw] at hA
    have hr := (hY.bring (ropes G u _ _) (ropes G v _ _) (Crown.tail (v:=n) F C hf q W hP) g).drop hx
    have ht := hA.plus hr; convert ht using 1; ext1 x; change A i G x.val=lop F n (f x)+ (A i G x.val-lop F n (f x)); abel
  intro q i
  obtain ⟨g,p⟩:= V G hv (by
    have hl:N.val≤P.val:=by rw [G.exact_size]; exact Nat.le_mul_of_pos_right _ G.count.property
    change _ < P.val*2; omega) q.val (portland G q.property (min_le_left ..)) ((curveD G e).home i)
  refine ⟨g,?_⟩; change _/|e| ≤ w; rw [abs_of_pos he]; exact (div_le_iff₀ he).mpr p
lemma pay_small (p: BoxD L u v A)(V:∀ i {N P:Side}(G: Ratio N P),G.count=L→ k≤N.val→ A i G (vacancyY N P)=0)(h:0<r) :∃ d m:ℝ,0<d∧0<m∧∃ n,IndexB L u v A d r m n :=by
 obtain ⟨a,C,e,ha,hC,he,l,H⟩:=p
 have hc:0≤quota:=(by norm_num:(0:ℝ)≤16) |>.trans quota_bound
 obtain ⟨w,ρ,d,hρ,hT,hd,hg,hP⟩:=clips hC.le ha hc h
 obtain ⟨m,hb,-,n,W⟩:= anchor_dusk (L:=L) (u:=u) (v:=v) (A:=A) (k:=max k l) (fun i _ _ G hx p=> H i G hx ((le_max_right ..).trans p)) 0 le_rfl (fun i _ _ G he hv=> by rw [V i G he ((le_max_left ..).trans hv),norm_zero]) he w d ρ hρ hT.le hd hg
 exact ⟨d,m,hd,hb,n,fun i _ _ G hc hv=> (W i G hc hv).books (by simpa only [zero_add,two_mul] using hP)⟩ -- tune
end YM.CF.Dial
