import YM.CF.BProof.Charge.Roll

/-! Gap per-column variables and exact severe membership. `Dry` for soft angular rows on
admitted fields keeps full data including log representation. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Angular.Yard
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Charge Charge.Form
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
local notation "Cl"=> SU.group.colorScale
variable {s:Side}(Y:Yard s)(κ y:ℝ)(U:Config G s)

-- this predicate ONLY Haar angular
abbrev scaleD := κ*thresh y
def Dry (b:Y.Col):= ∀ i:Y.Apt, cd G (mag y (Y.inter (b,i))) (U (Y.inter (b,i)))≤scaleD κ y -- bg y i.2

def severe := univ.filter (fun b=> ¬ Y.Dry κ y U b)
lemma desert (i:Y.Col): i∉Y.severe κ y U↔ Y.Dry κ y U i:=by simp [severe]
lemma wind (i:Y.Col): i∈Y.severe κ y U↔∃ a, scaleD κ y<cd G (mag y (Y.inter (i,a))) (U (Y.inter (i,a))):=by simp [severe,Dry]
lemma desert_m (i:Y.Col): MeasurableSet {U:Config G s|i∈Y.severe κ y U}:=by
 simp_rw [wind]; simp only [Set.setOf_exists]; apply MeasurableSet.iUnion; intro a; apply measurableSet_lt measurable_const; unfold cd; fun_prop
lemma deserts {V:Config G s}(e:Set.EqOn U V ↑Y.field): Y.severe κ y U=Y.severe κ y V:=by
 have h(i:Y.Door):= e (Y.inter_mem i); ext x; simp only [mem_filter,severe,mem_univ,Dry,h]

/-- paid angular data and formal arguments (zero spending on severe still in caller). -/
structure Evap (κ y:ℝ)(U:Config G s)(W:Y.Branch): Prop where
  enough : 0<κ
  margin : scaleD κ y+xi y ≤ thresh y/16
  pay (b:Y.Door) (h:b.1∉Y.severe κ y U) : U (Y.inter b)=mag y (Y.inter b)* SU.group.lieExp (W b)
  small (b:Y.Door)(h:b.1∉Y.severe κ y U): ‖W b‖≤thresh y

variable {S:Hall s} {F:Y.FaceS}
variable {U} {κ y:ℝ} (W:Y.Branch) (e:Y.Climate y S U F)(s₀:Y.Evap κ y U W)
include s₀
lemma thirst (b:Bond s) (h:cd G (mag y b) (U b) ≤ xi y)(g:Y.roll W b=0): Tone (Y.roll W) y b U :=by
 have ht:=s₀.margin; have hp:0<κ:= s₀.enough; have hg:0<thresh y:=coin_pos ..; refine ⟨h.trans ((le_add_of_nonneg_left (by unfold scaleD; positivity)).trans ht),by rw [g,norm_zero]; exact hg.le,by simpa only [g,Gauge.mat_lieExp_zero,mul_one] using h⟩
lemma temper (b:Y.Door)(h: b.1 ∉ Y.severe κ y U) : Tone (Y.roll W) y (Y.inter b) U:=by
 have hp:0<xi y:=coin_pos ..; have ht:cd G (mag y _) (U _)≤_:= (desert Y κ y U _).1 h b.2; refine ⟨ht.trans ((le_add_of_nonneg_right hp.le).trans s₀.margin),by rw [roll_inter]; exact s₀.small b h,by rw [Y.roll_inter,s₀.pay _ h,cd_self]; exact hp.le⟩

variable (i:Y.Index)(x:Per s)(p:Space s)
include e
lemma tone_gap (h:Y.Gap i x)(n:TAxis)(p':(i,p)∉Y.severe κ y U): Tone (Y.roll W) y (horiz x p n) U:=by
 let a:=Y.depth i x; by_cases k: a=0
 · apply thirst Y W s₀
   · have hk':x=Y.dEnd i:=(Y.at_depth i x h).symm.trans (by unfold a at k; rw [k,Y.atD_zero]); subst x; unfold dEnd; split<;>rename_i ht
     · exact haven Y y S U F e i ht _ ((wet_h ..).2 (Y.u_in i).le)
     exact haven Y y S U F e (i+1) ((Y.next i).2 ht) _ ((wet_h ..).2 (by simp))
   rw [roll_h Y i x p n W h, consult,show Y.depth i x=0 from k, proj0]; rfl -- arg order tune
 let b: Fin Y.short:=⟨a-1,by unfold a; have hv:=Y.depth_le i x h; unfold a at k; omega⟩; have hb:b.val+1=a:=by change a-1+1=a; omega
 let B:Y.Door:= ((i,p),b,n); have ht:Y.inter B=horiz x p n:=by unfold inter reach B; dsimp only; rw [hb,at_depth]; exact h -- tune
 rw [←ht]; exact temper Y W s₀ B p'
omit s₀ -- ?
include s₀
lemma tone_vert {r:ℕ}(hv:4*r+4≤Y.long)(h:Y.Vic i r x) : Tone (Y.roll W) y (vert x p) U:=by
 apply thirst Y W s₀ _ _ (Y.roll_v x p W)
 rcases Y.edge_from x with a|a <;> generalize Y.twinsBand x=j at a
 · change along (Y.u j) x<Y.long at a; by_cases k:Y.D j; exact haven Y y S U F e j k _ ((wet_v _ _ Y.lL).2 a); rw [mag_v]; have h':(U (vert x p))=1:= e.flat (Y.trunk_b p k a ?_); rw [h',cd_self]; exact (coin_pos ..).le -- term placeholder
   unfold Cut cut; rcases Y.vic_split i r x (by omega) h with u|u|u
   · have hp:i=j:= (Y.u_part i _ u.2).symm.trans (Y.u_part j x a.le); subst j; have he:=Y.before_u i u.2; have hz:=u.1; omega
   · rcases Y.common j x a.le u with ⟨q,_⟩|⟨q,_⟩ <;> subst x
     · simp only [along_self]; omega
     rw [Y.u_in j] at a; omega
   have h:i+1=j:= (Y.u_part (i+1) x u.2).symm.trans (Y.u_part j x a.le); subst j; have he:=u.1; omega
 rw [mag_v,show U (vert x p)=1 from e.flat (Y.trunk_g p a),cd_self]; exact (coin_pos ..).le

/-- N collar. copies from nEnd. -/
lemma tone_band {n:TAxis}{b:Bool}(k:Y.Band i x)(hq:flag (Y.u i) x Y.long=b)(hv:angle Y.long (along (Y.u i) x)=if b then 1 else 0)(g:(Y.location i b,p)∉ Y.severe κ y U) : Tone (Y.roll W) y (horiz x p n) U:=by
 let d:=Y.location i b; by_cases u:Y.D i
 · apply thirst Y W s₀ _ (haven Y y S U F e _ u _ ((wet_h ..).2 k)); rw [roll_c,heir_h,find_band _ i x p n k,delegate,if_pos u]; rfl
 let Z:Y.Door:= ((d,p),Y.lastDepth,n); let v:=Y.u i; let l:=Y.long; let t:=front v l b; let M:= Y.inter Z
 have hx: M=horiz t p n:=by unfold M inter reach Z; dsimp only; rw [last_depth,atD_full,gFrame]; exact u -- tune
 have hB:Y.roll W (horiz x p n)= W Z:=by rw [roll_c,heir_h,find_band _ i x p n k,delegate,if_neg u,hq,projs]; rfl
 have hm:mag y (horiz x p n)=mag y M:= by rw [hx,mag_h,mag_h]
 have hi:cd G (U M) (U (horiz x p n))≤xi y:=by rw [hx]; exact copy Y y S U F e x i k u b hq hv (p,n)
 refine ⟨by rw [hm]; exact (cd_triangle G _ (U M) _).trans ((add_le_add (show cd G (mag y M) (U M)≤scaleD κ y from Y.desert κ y U Z.1 |>.1 g Z.2) hi).trans s₀.margin),?_,?_⟩
 · rw [hB]; exact s₀.small Z g
 rw [hB,hm,← s₀.pay _ (show Z.1∉_ from g)]; exact hi
lemma tone_horiz (n:TAxis){r:ℕ}(v:4*r+4 ≤Y.long)(g:Y.Vic i r x)(u:(i,p)∉Y.severe κ y U) : Tone (Y.roll W) y (horiz x p n) U:=by
 rcases Y.vic_split i r x (by omega) g with h|h|h
 · obtain ⟨a,b⟩:=Y.cold_flag i x (by omega) h; exact Y.tone_band W e s₀ _ x p h.2 a b u -- tune
 · exact Y.tone_gap W e s₀ _ x p h n u
 obtain ⟨a,b⟩:=Y.hot_flag _ x (by omega) h; exact Y.tone_band W e s₀ _ x p h.2 a b (by simpa only [location, Bool.false_eq_true, ite_false, add_sub_cancel_right] using u)
end YM.CF.BProof.Angular.Yard
