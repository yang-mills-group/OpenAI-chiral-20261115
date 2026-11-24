import GaugeFieldConstruction.DelawareRT
/-!
 # Interior chart o (Full n already contains y slot); w complex time difference only x position; χ constant rel-space v ALWAYS real.
 # ± packaged `(g:Bool)` = false for original (W earlier T to left) ⇒ Im w <0. true = tilt ⇒ Im w>0.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Mink Function Set Filter MeasureTheory Complex Finset Distribution Probe Surface
open scoped Topology BigOperators ContDiff InnerProductSpace NNReal ENNReal
abbrev skyIRT (i:Fin 3):Space3:= spatial (basis i.castSucc)
@[simp] lemma timeSkyRT (i:Fin 3): time (basis i.castSucc)=0:=by simp [time, show timeAxis≠ i.castSucc from (Fin.castSucc_ne_last i).symm]
lemma posIRt (i:Fin 3): position (skyIRT i) 0=basis i.castSucc:=by rw [← timeSkyRT i]; exact position_eta _
variable {n:ℕ}(k:Fin n)
local notation "ιᵢ" => k.castSucc
local notation "ιⱼ" => k.succ
local notation "N"=> τNearRT k
local notation "W_A"=>Full (n+1)
noncomputable def τBoostXRt : Full n →L[ℂ] Full (n+1):= LinearMap.toContinuousLinearMap {
 toFun x:= WithLp.toLp 2 fun i=> k.castSucc.insertNth (α:=fun _=> ℂ) (x (k,i.2)) (fun j=> x (j,i.2)) i.1
 map_add' a b:=by ext1 ⟨i,s⟩; cases i using Fin.succAboveCases k.castSucc <;>simp
 map_smul' a x:=by ext1 ⟨i,s⟩; cases i using Fin.succAboveCases k.castSucc <;>simp
}
-- orientations
abbrev dayRT (k:Fin n)(g:Bool):Fin (n+1):= if g then k.succ else k.castSucc
abbrev ΛNamePRt (k:Fin n)(g:Bool)(x:Full (n+1)):= if g then (τNearRT k).name x else x
noncomputable def BurstIRt (x:Fin (n+1))(d:E4):Full (n+1):= penΛ (n+1) (PiLp.single 2 x d)
noncomputable def QchIRt (g:Bool)(w:ℂ×Full n)(u:Space3):Full (n+1):= ΛNamePRt k g (τBoostXRt k w.2 + (BurstIRt ιᵢ (position u 0) + w.1 • realDirΛ ιᵢ timeAxis))
-- real-linear calc
noncomputable abbrev addMeterRT := κMoverRT k
lemma nameIRT (x y:Points (n+1)): (N).name (glow x y)=glow ((N).switch x) ((N).switch y):= by simp [NearPair.name]
lemma χBornRT (w:ℂ×Full n)(u:Space3): QchIRt k false w u= glow (addMeterRT k (position u w.1.re, reality w.2)) (addMeterRT k (position 0 w.1.im,shade w.2)):=by
 have hPos(t:ℝ)(u:Space3):position u t=t • basis timeAxis+position u 0:= ext_by (by simp) (by simp)
 have hE: position 0 0=0:= ext_by (by simp) (by simp)
 ext1 ⟨i,j⟩; unfold QchIRt addMeterRT; rw [motionKnownRT,motionKnownRT,hPos w.1.re,hPos w.1.im, hE]; cases i using Fin.succAboveCases k.castSucc <;>simp [τBoostXRt,BurstIRt,penΛ,ΛNamePRt,realDirΛ,Points.direction,addXRT,glow,BurstIRt,k.castSucc.succAbove_ne,reality,shade]
 all_goals apply Complex.ext <;> simp [add_comm] <;> first|rfl|exact add_comm .. 
#print axioms QchIRt
lemma χTiltBornRT (w:ℂ×Full n)(u:Space3): QchIRt k true w u= glow ((N).switch (addMeterRT k (position u w.1.re,reality w.2))) ((N).switch (addMeterRT k (position 0 w.1.im,shade w.2))):=by
 rw[show QchIRt k true w u= (N).name (QchIRt k false w u) from rfl, χBornRT,nameIRT]
noncomputable def NameΛShellRT (k:Fin n)(g:Bool): Full (n+1) →L[ℂ] Full (n+1):= LinearMap.toContinuousLinearMap {
 toFun:= if g then fun z=> WithLp.toLp 2 fun i:Fin (n+1)×Axis=>z ((τNearRT k).s i.1,i.2) else fun z=>z
 map_smul' a b:=by ext; cases g<;>rfl
 map_add' a b:=by ext; cases g<;>rfl
 }
lemma shellPaintRt (g:Bool)(x:Full (n+1)): ΛNamePRt k g x= NameΛShellRT k g x:=by
 cases g
 · rfl
 ext1 ⟨i,j⟩; change glow _ _ _= x ((N).s i,j); apply Complex.ext <;> simp[glow] <;> rfl
lemma shellDirRt (g:Bool)(i:Axis): NameΛShellRT k g (realDirΛ ιᵢ i)= realDirΛ (dayRT k g) i:=by
 cases g
 · rfl
 rw [← shellPaintRt]; change (N).name (glow _ _) = _; rw [nameIRT, switchDirRT,map_zero]; rfl
lemma liftχRt (w:ℂ×Full n)(u:Space3): shade (QchIRt k false w u)= addMeterRT k (position 0 w.1.im,shade w.2):=by rw [χBornRT,im_glow]
lemma κDawnRT (y: Heights (n+1))(v:(τNearRT k).Fleck y): addMeterRT k (position 0 0,dawn (remΛ k.castSucc y)) = dawn y:=by
 rw [addMeterRT, motionKnownRT]; ext1 i
 cases i using Fin.succAboveCases k.castSucc <;> simp [addXRT,dawn,place, show position 0 0=0 from ext_by (by simp) (by simp), remΛ,tNextRT, ← (show y ιᵢ=y ιⱼ from v.willing.1)]
lemma centχRT (o:Points n)(y:Heights (n+1))(v:(τNearRT k).Fleck y)(u:Space3): QchIRt k false (0,glow o (dawn (remΛ k.castSucc y))) u=glow (addMeterRT k (position u 0,o)) (dawn y):=by rw [χBornRT]; simp only [zero_re,zero_im,re_glow,im_glow]; rw[κDawnRT k y v]
lemma centRoomRT (o:Points n)(u:Space3)(g:u ≠0): addMeterRT k (position u 0,o) ∈ (τNearRT k).gap:=by
 change _-_∈ Mink.spacelike; unfold addMeterRT; rw [show (κMoverRT k _).ofLp (N).j=o k from mosJRt k (position u 0,o), show (κMoverRT k _).ofLp (N).i=_ from mosIRt k (position u 0,o), sub_add_eq_sub_sub,sub_self,zero_sub,lateral]; simp [g]
abbrev HalfRT (g:Bool): Set ℂ:= if g then {z|0<z.im} else {z|z.im<0}
lemma halfOpenRT (g:Bool): IsOpen (HalfRT g):= by cases g; exact isOpen_lt (by fun_prop) continuous_const; exact isOpen_lt continuous_const (by fun_prop)
lemma zeroHRT (g:Bool):0∈closure (HalfRT g):=by
 let D(t:ℝ):ℂ:= if g then t*I else -(t:ℂ)*I
 have p: MapsTo D (Ioi 0) (HalfRT g):= by
    intro i ht; cases g <;> simp [HalfRT,D, show 0 < i from ht]
 have t:D 0=0:=by cases g<;>simp [D]
 rw[← t]; exact p.closure (by cases g<;>simp only[D,Bool.false_eq_true,↓reduceIte]<;>fun_prop) (by simp)
lemma roomXRt (o:Points n)(y:Heights (n+1))(v:(τNearRT k).Fleck y)(g:Bool): ∀ᶠ w : ℂ×Full n in 𝓝 (0,glow o (dawn (remΛ k.castSucc y))),w.1∈ HalfRT g→∀ u:Space3,QchIRt k g w u ∈tube (n+1):=by
 let H(w:ℂ × Full n):=addMeterRT k (position 0 w.1.im,shade w.2); let U(w:ℂ× Full n):=if g then (τNearRT k).switch (H w) else H w
 have hU:Continuous U:=by
    have A: Continuous H:=by
       apply (addMeterRT k).continuous.comp; refine Continuous.prodMk ?_ ((cont_sh n).comp continuous_snd); exact divide.symm.continuous.comp (continuous_const.prodMk (Complex.continuous_im.comp continuous_fst))
    cases g; exact A; exact (τNearRT k).switch.continuous.comp A
 let w:ℂ × Full n:=(0,glow o (dawn (remΛ k.castSucc y)))
 have eqH: H w= dawn y:=by simp only [H,w,im_glow,zero_im,κDawnRT k y v]
 have eqU: U w=dawn y:=by cases g<;>simp_all [U,heightTieRT]
 -- all other order
 have hp: ∀ i j:Fin (n+1), ∀ᶠ z in 𝓝 w, i<j→(i ≠ ιᵢ ∨ j ≠ιⱼ) → U z j-U z i∈ Mink.inside:=by
    intro i j; by_cases p: i<j ∧ (i ≠ιᵢ ∨ j≠ιⱼ)
    · skip
      have hc: U w j-U w i∈ Mink.inside:=by rw [eqU]; unfold dawn inside; simp [place,sub_eq_add_neg,v.willing.2 i j p.1 p.2] -- done
      filter_upwards [((show Continuous fun z => U z j-U z i by fun_prop).tendsto w).eventually (Mink.open_inside.mem_nhds hc)] with z hz; exact fun _ _=>hz
    exact Eventually.of_forall fun z h t=> (p ⟨h,t⟩).elim
 filter_upwards [eventually_all.mpr (fun i=>eventually_all.mpr (hp i))] with z hz h u
 have he:shade (QchIRt k g z u)=U z:=by cases g; exact liftχRt ..; rw[χTiltBornRT,im_glow]; rfl
 change shade _ ∈ fields _; rw [he]; simp only[fields, Set.mem_iInter, Set.mem_setOf_eq]; intro i j hi
 by_cases p:i≠ιᵢ ∨ j≠ιⱼ; · exact hz i j (show i.val < j.val by omega) p
 push Not at p; rw [p.1,p.2]; cases g
 · change H z (ιⱼ)- H z (ιᵢ) ∈ _; unfold H addMeterRT; rw[mosJRt,mosIRt]; simp [sub_add_eq_sub_sub,inside,show z.1.im<0 from h]
 change (N).switch (H z) ιⱼ - (N).switch (H z) ιᵢ ∈ _; simp only[NearPair.switch_at,switchNextRt,switchNextRt']; unfold H addMeterRT; rw [mosIRt,mosJRt]; simp [inside,show 0<z.1.im from h]
#print axioms roomXRt
end YM.NSF.Boundary
end
