import YM.CF.Jet.Operetta
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Function Filter Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Phase Phase.Sample Lattice Cube Broc Drapes Tulip Peaks
open scoped Topology Matrix BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
set_option synthInstance.maxSize 8000
attribute [local instance] opCStarAlgebra

def Me(n:ℕ)(B e:ℝ){N P:Side}(G:Ratio N P):Draw (Loom G e):=⟨fun E _ _ _ V q=>∀ x∈V,
  TransK n (fun i=>(q i).val.1.1) x B∧TransK n (fun i=>(q i).val.1.2) x B∧seek (fun i=>(q i).val.2.1) n x B∧seek (fun i=>(q i).val.2.2) n x B⟩
lemma vw(n:ℕ){B a K e:ℝ}(hB:0≤B)(p:0<a)(pe:0<e):∃ V:ℝ,1≤V∧∀ {N P:Side}(G:Ratio N P)(A:Bale N P→Op (Iota G))(u:AxisT), Crown (badge (zoneP G e)) (rope G u e) (rope G u e) a K (fun x=> A x.val)→ Screen (weave G e) (Me n B e G) n (fun i=> Matrix.trace (A (post i.val))) (a/2) (V*quartzK a K):=by
 obtain ⟨C,T,H⟩:=blend_r B hB n
 let t:ℝ:=(1+2^n/e)^n
 let V:=max 1 (composeCost n t C)
 refine ⟨V,le_max_left ..,fun {N P} G A u ht=>?_⟩
 let f(x:Loom G e): TopK G e:=⟨post x.val,x.val,x.property,by simpa using pe⟩
 obtain ⟨F,D,q,W,r⟩:=ht; let Q(S:Seal (Site (More P)))(x:Loom G e):=(F S (f x)).trace
 have hp:0≤V:=le_max_of_le_left zero_le_one
 refine ⟨Q,fun S=>V*ledgerV (D S),fun S=>?_,fun i=> ?_,fun i=> Eq.trans (congrArg Matrix.trace (r (f i))) (Matrix.trace_sum ..)⟩ -- diag
 · have he:= ledgerT (q S).toTicket
   refine ⟨⟨mul_nonneg hp he.posT,fun p=>he.conduct (right_ne_zero_of_mul p), he.continuousE.comp ((post_c.comp continuous_subtype_val).subtype_mk _),fun x=> (he.norms (f x)).trans (le_mul_of_one_le_left he.posT (le_max_left ..)),fun x y p=>?_,fun x g=>?_⟩,?_⟩
   · have hv:= he.varies (f x) (f y); rw [show (curveD G e).eval S (f x) (f y)=0 from (by change bookK _ _ _ S / _=0; rw [paid_zero G e x y S p,zero_div]),mul_zero] at hv; exact sub_eq_zero.mp (norm_le_zero_iff.mp hv)
   · have hp: f ((weave G e).dress g x) = (curveD G e).drive g (f x):= Subtype.ext (speak G g _).symm
     exact (congrArg (fun i=>Matrix.trace (F S i)) hp).trans (he.gauge g _)
   intro E _ _ _ U h d q' x hx
   let X(i:E):= post (d i).val
   have hy : Allows n X x C:= H E _ _ (fun i=>(d i).val) x (q' x hx).1 (q' x hx).2.1 (q' x hx).2.2.1 (q' x hx).2.2.2
   have hk : ball (X x) e⊆ zoneP G e:= fun z g=>⟨(d x).val,(d x).property,by rw [mem_ball,dist_eq_norm] at g; exact g⟩
   have ht i j : Allows n (fun x=> F S (f (d x)) i j) x (V*D S i j):=by
     let Φ:= fun x=> F S x i j; let c:=D S i j
     have hl:Allows n (equalizer Φ ∘ X) x (composeCost n (c*t) C):= (allows_looks (q S|>.fuel i j) ((q S).expo i j).connected hk pe n ((q S).expo i j).bounded).comp (f:=X) hy
     apply (hl.mono ?_).germ _
     · calc
         composeCost n (c*t) C=composeCost n t C*c:=by unfold composeCost; ring
         _ ≤ _:=mul_le_mul_of_nonneg_right (le_max_right ..) ((q S).expo i j).positive
     filter_upwards [] with z
     exact dif_pos (f (d z)).property
   let hA := allows_sum (f:=fun i x=> F S (f (d x)) i i) (s:=Finset.univ) (fun i _=>ht i i)
   apply hA.mono; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (sum_le_sum fun i _=> single_le_sum (f:=fun j=>D S i j) (fun j _=>(q S).nonn i j) (mem_univ i)) hp
 unfold hitE; simp_rw [mul_left_comm (Branch.rent ..) V,←mul_sum]; exact mul_le_mul_of_nonneg_left (Branch.tall (s:=rope G u e) (P:=F) (fun S=>(q S).toTicket) W p (cD G e) quota_p.le i) hp
end YM.CF.Jet
