import YM.SU5.Relativistic.Inkstand
import YM.SU5.Relativistic.Serifs
/-!
# Purchase certificate of payload (layout to follow). A proof of sign in
*all* orientations uses flatAcross, but this test is on two axis-windows.
Want Pre election finite estimates. Result for any n holonomic.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.ScreeV
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Lifted Afterglow Tapestry Branch Tenant Skye Cliplet RG Brace Crest Crest.Sleet Crest.Sleet.UpStart Satin
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {n:Side}(K:Calibration)(F:Waxy){k:ℕ}(U:Fin k→ Cover)(c:Fin 3)(A:ℕ)(u:Cover)
-- careful products: calibrated ordering now. data at representative via Camera.
abbrev prompter(i:Fin k):=1+gyre K (U i) c * glebe K u (U i) F A c
def billboard : Buffered.Family K:= (List.ofFn (prompter K F U c A u)).prod
local notation "B"=>billboard K F U c A u
lemma billed (S:Finset Cover)(s:Finset ℤ)(q:∀ i∈plusHalf,∀ j:ℤ,j∉s→ F i j=0)(p:∀ i,nodeC (U i)∈S)(h:∀ i, viabox (district s (U i) F) u⊆ S) : InTest K false S false B:=by
 let X(i):= prompter K F U c A u i
 have ht (i):InTest K false S false (X i):= (InTest.one).add (((gyre_T ..).mono (singleton_subset_iff.mpr (p i))).mul ((glebe_T K u (U i) F A c s q).mono (h i)))
 have hv(l:List (Fin k)): InTest K false S false (l.map X).prod:=by induction l with|nil=>exact .one|cons i l ih=>exact (ht i).mul ih
 have hx:=hv (List.ofFn id); rw [List.map_ofFn] at hx; exact hx
lemma bill_at (m:Side)(x:Fields (K.c m)): B m x= (List.ofFn (fun i=> prompter K F U c A u i m x)).prod:=by
 let P(i):= prompter K F U c A u i
 have h(L:List (Fin k)): (L.map P).prod m x=(L.map (fun i=> P i m x)).prod:=by induction L with| nil=>rfl| cons i L ih=> rw [List.map_cons,List.map_cons,List.prod_cons,List.prod_cons,Pi.mul_apply, Pi.mul_apply,ih]
 have ht:=h (List.ofFn id); simp_rw [List.map_ofFn] at ht; exact ht
lemma bill_neutral : Neutral K B:=by
 intro m g x; rw [bill_at,bill_at,map_list_prod,List.map_ofFn]; congr 2; funext a; change 1+(gyre K (U a) c m _)*(glebe K u (U a) F A c m _)= twist (quantU (tradew _ g)) (1+(gyre K (U a) c m x)*(glebe K u (U a) F A c m x)); rw [map_add,map_mul,map_one]; apply congrArg (fun z:FC (Single (K.c m))=>1+z); exact congrArg₂ (· * ·) (gyre_N K _ _ m g x) (glebe_N K u _ F A c m g x) -- tune
abbrev AWork (m:Side)(S:Finset Cover):Cliplet (K.c m) k:= ⟨region S (K.c m), fun i=>wrap (More (K.c m)) (nodeC (U i)),false,B m⟩
lemma warrant (m:Side)(C S:Finset Cover)(p:Set.InjOn (wrap (K.c m)) C)(s:Finset ℤ)(q:∀ i∈plusHalf,∀ j:ℤ,j∉s→F i j=0)
    (hx:∀ i,U i∈C ∧ nodeC (U i)∈ S)(hL:∀ a,∀ z∈district (TwistT A) (U a) F,z∈ C∧nodeC z∈S∧ march (wrap (More (K.c m)) u) (wrap (More (K.c m)) (nodeC z)) 1=TrackV u z)
    (v:∀ i, viabox (district s (U i) F) u⊆ S)(l d:ℕ)(t:∀ a,∃ f:Fin k→ WalkA, f a=0∧∀ i, U i=U a+tack ((d:ℤ) • f i) 0)
    (V Z R:ℝ)(e:0≤ Z)(r:V+Z≤R)
    (s0:∀ D:Finset WalkA, ∑ x∈D,‖F 2 0 ((d:ℤ) • x)-(if x=0 then 1 else 0)‖^2 ≤ Z^2)
    (j:ℕ)(M:Tulip.Male)(p₁:IsStarProjection (spar j M (1:Pane (K.c m))))
    (uF:∀ i:Fin k,∀ s:SU.Slot, ‖strum (K.c m) (U i) A F s‖≤ V)(hF:∀ i:Fin k,∀ s:SU.Slot, let X:=strum (K.c m) (U i) A F s; ‖acts (spar j M (1:Pane (K.c m))) X-X‖≤Z)
    (w μ ν:ℕ)(γ γ' τ:ℝ): let W:=AWork K F U c A u m S
    Injective W.birth → Sparse l W.s → Lattice.halo (w+l+1) W.s⊆ W.broad →
    (∀ V:Pane (K.c m), W.feel τ ν V→ let G:=Lattice.gauge (stampG (wrap (More (K.c m)) u) V) V; Rightful W.broad G 1 γ ∧ Rightful (hot W μ) G 1 γ')→
     Column j M w l μ ν γ γ' τ (3*Z) R W:=by
 intro W h s₁ g he
 have hv:Injective U:= fun i j e=> h (show wrap (More (K.c m)) (nodeC (U i))=wrap (More (K.c m)) (nodeC (U j)) from (by rw [e]))
 refine ⟨(billed K F U c A u S s q (fun i=>(hx i).2) v).support m,h,s₁,g,fun x=>?_⟩
 let n:=K.c m; choose Y hY tY qY vY cY using (fun i b=>pickClamp d A (K.c m) F S C U p hv c Z V hx i (fun z p=> ⟨(hL i z p).1,(hL i z p).2.1⟩) (t i) b e s0 _ p₁ (uF i _) (hF i _))
 let U₀:= stampG (wrap (More n) u) x.1; let T₀:= tradew n U₀; let X(i:Fin k)(l:Ring5):= basisC n (U i) 2 (barred c l)
 let p'(i:Fin k)(l:Ring5):= acts (star T₀.val) (X i l)
 let z(i:Fin k)(l:Ring5):= acts (star T₀.val) (Y i l)
 have hT(i l): acts T₀.val (p' i l) = X i l:=act_starUnit ..
 have ht(i l):acts T₀.val (z i l)=Y i l:=act_starUnit ..
 have hP(i l): trim (hand true (cutM (Tset n))) (p' i l):= sense (t:=U₀) (b:=true) |>.1 (show _ from (by rw [show (tradew n U₀)=T₀ from rfl, hT]; exact b_down n 2 (by decide) (U i) _)) -- tune
 refine ⟨U₀,p',z,he _,?_,fun i b=>?_,hP,fun i l=>?_,fun i l=>?_,fun i l=>?_,fun i l i' l'=>?_,fun i l=>?_⟩
 · change B m x= xpert (fun i=> prime (fun d=> handy false (Tset n) (p' i d) (z i d)))
   rw [bill_at]; unfold xpert; congr 2; funext i; rw [honour (hP i)]; change 1+ ((gyre K (U i) c) m x)* ((glebe K u (U i) F A c) m x)=_; apply congrArg (fun z:FC (Single (K.c m))=>1+z); refine congrArg₂ (fun a b:FC (Single (K.c m))=>a*b) ?_ ?_
   · rw [gyre,bind_v]; have hn:= fixF n U₀ (U i) 2 c -- orientation inverse needs star
     have hu : star T₀= tradew n U₀⁻¹:= by
       have h:T₀*tradew n U₀⁻¹=1:= (Hive.trade_c U₀⁻¹ U₀).trans (by rw [mul_inv_cancel,Hive.trade_p])
       exact mul_left_cancel (show T₀*star T₀=T₀*tradew n U₀⁻¹ from (mul_inv_cancel T₀).trans h.symm)
     unfold p'; rw [show star T₀.val=(tradew n U₀⁻¹).val from congrArg Subtype.val hu]; exact (fixF n U₀⁻¹ (U i) 2 c).symm
   rw [glebe,bind_v]; congr 2; funext b; rw [august_probe K u (U i) F A c m b (fun z g=>(hL i z g).2.2)]; congr 1; rw [← hY]; change acts (star T₀.val) (acts (cutM (Tset n)) _)=acts (cutM (Tset n)) (acts (star T₀.val) _); apply act_field (T:=star T₀); nth_rw 1 [←gauge_frostT U₀]; exact twist_inv T₀ _ -- rewrite goal investigate
 · unfold cargo; let b₀:= nodeC (U i); have hx:withinM (modesIn n {W.birth i}) (X i b):= by
     have ha: {W.birth i}=region {b₀} n:= by unfold region; rw [Finset.image_singleton] <;> rfl
     rw [ha]; exact b_broad n (U i) _ (mem_singleton_self _) _ _
   apply coverSense (t:=U₀)|>.1; rw [hT]; exact hx
 · rw [show p' i l=acts (star T₀).val _ from rfl,act_unit_norm]; change ‖X i l‖≤1; unfold X basisC; rw [norm_smul]; simp [basisKet,Lifted.winding,Rush.fee_norm] -- tune norm winding
 · apply coverSense (t:=U₀) |>.1; rw [ht]; exact vY i l
 · exact ((act_unit_norm (star T₀) _).le.trans (qY i l)).trans r
 · rw [←act_unit_inner T₀,hT,ht]; exact cY ..
 simp only; rw [show acts (tradew _ _).val (z i l)=_ from ht i l]; exact tY i l
end YM.CF.Pannier.Chancel.ScreeV
#print axioms YM.CF.Pannier.Chancel.ScreeV.warrant
