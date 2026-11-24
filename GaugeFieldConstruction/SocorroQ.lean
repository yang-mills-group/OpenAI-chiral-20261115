import GaugeFieldConstruction.WhelmQ
import GaugeFieldConstruction.WallabyQ
import GaugeFieldConstruction.AndrosJ
import GaugeFieldConstruction.BootHearthJ
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4200
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock
namespace WallsQ
variable {w:ℕ}{K:Calibration}{o:Cover}{m d:Side}
-- maximum over ANY value satisfying scored definition (not requiring color constants initial locations), empty profit 0. List enumeration.X
local instance (d:Side):NeZero (2*d.val):= ⟨(mul_pos (by decide) d.property).ne'⟩
local notation "DK"=> dialQ d
variable {C:Type} [Fintype C][Nonempty C]{L:Loom (K.c m)}{E:Mark (K.c m)→ℂ}{Price:ℝ}
variable (D:Metered K m L E Price)
variable {col:C → Cover}{mtr:C→Family K}{S:C→Finset Cover}{A:C→ℝ}{u:C→ℝ}
variable (p₀: ∀ i,0 ≤ A i) (hu:∀ i, 0 < u i)
variable (e:∀ i:C, InTest K true (S i) false (mtr i)) (c:∀ i:C, pay (mtr i) (A i)) (h:∀ i,PipeQ K w o (col i) (S i))
variable {x:dialQ d→C}{M:dialQ d→Family K}
def useinQ {u:Type}[Fintype u](l:List u):= (∀ y:u,y∈l)∧ l.Nodup
lemma permUseQ {b:Type}[Fintype b]{l r:List b} (t:useinQ l)(u:useinQ r):l.Perm r:=List.perm_of_nodup_nodup_toFinset_eq t.2 u.2 (Finset.ext (fun i=>by simp [t.1 i,u.1 i]))
def tentPegQ (α:ℕ)(P:Cover)(K:Calibration){C:Type} (col:C → Cover) (mtr:C→Family K)(d:Side)(x:dialQ d→ C) (M:dialQ d→Family K):Prop:=∀ j:dialQ d,TwigQ K α P (col (x j)) (mtr (x j)) d j (M j)
variable (p:tentPegQ w o K col mtr d x M) {Ω:List (dialQ d)}(l:useinQ Ω)
include p e h
local notation "payd" Ω:max m:max=> List.prod (List.map m Ω)
local notation "Hi" F:max=> E ((F:Family K) m)
private lemma quals (j:dialQ d):TestFamily K true (M j):=by obtain ⟨a,q,z⟩:=p j; obtain ⟨b,u,h⟩:= z.lives (e _) (h _); exact aux_test u
lemma perm_tent {α Λ:List (dialQ d)}(z:α.Perm Λ): (α.map M).prod=(Λ.map M).prod:= (z.map M).prod_eq' (List.pairwise_map.mpr (by
    suffices q:∀ l:List (dialQ d), l.Pairwise (fun i j=>Commute (M i) (M j)) from q α
    intro l; induction l with|nil=>constructor|cons u l ih=> exact List.pairwise_cons.mpr ⟨fun _ _=> even_tests _ (quals e h p _) (quals e h p _),ih⟩))
-- drill lists split
omit p e h
private def yesL (l:List (dialQ d))(j:Axis)(v:ℤ):= l.filter (fun y=>decide (posQ d j v y))
private def nonL (l:List (dialQ d))(j:Axis)(v:ℤ):= l.filter (fun y=>decide (¬posQ d j v y))
include l
private lemma sameLQ (j:Axis)(v:ℤ): useinQ (nonL Ω j v++ yesL Ω j v):=by
 refine ⟨?_,?_⟩
 · intro y; by_cases p:posQ d j v y <;> simp [yesL,nonL,p,l.1 y]
 rw [List.nodup_append']; refine ⟨l.2.sublist (List.filter_sublist), l.2.sublist List.filter_sublist,?_⟩; intro y t r; simp [yesL,nonL] at t r; exact t.2 r.2
private lemma mirrorListQ (j:Axis)(v:ℤ): useinQ ((yesL Ω j v).map (bendQ d j v) ++ yesL Ω j v)∧ useinQ (nonL Ω j v ++ (nonL Ω j v).map (bendQ d j v)):=by
 obtain ⟨ha,hb,hc⟩:= List.nodup_append'.1 (sameLQ l j v).2
 let b:=bendQ d j v; have h0(x:dialQ d):b (b x)=x:=bend_in _ _ _ _
 constructor <;> rw [useinQ,List.nodup_append']
 · refine ⟨?_,hb.map (bend_in d j v).injective,hb,?_⟩
   · intro y; by_cases p: posQ d j v y; exact List.mem_append_right _ (List.mem_filter.mpr ⟨l.1 y,decide_eq_true p⟩); apply List.mem_append_left; rw [List.mem_map]; exact ⟨b y,List.mem_filter.mpr ⟨l.1 _,decide_eq_true ((pos_refQ ..).mpr p)⟩, h0 y⟩
   intro y ht q; obtain ⟨u,v',rfl⟩:=List.mem_map.mp ht; simp only [yesL,List.mem_filter,decide_eq_true_eq,pos_refQ] at v' q; exact q.2 v'.2
 refine ⟨?_,ha,ha.map (bend_in d j v).injective,?_⟩
 · intro y; by_cases p: posQ d j v y
   · apply List.mem_append_right; rw [List.mem_map]; exact ⟨b y,List.mem_filter.mpr ⟨l.1 _,decide_eq_true (by unfold b; simp [pos_refQ,p])⟩, h0 y⟩
   exact List.mem_append_left _ (List.mem_filter.mpr ⟨l.1 _,decide_eq_true p⟩)
 intro y ht q; obtain ⟨u,v',rfl⟩:=List.mem_map.mp q; simp only [nonL,List.mem_filter,decide_eq_true_eq,pos_refQ,not_not] at v' ht; exact v'.2 ht.2
-- pow prices to Fee quotient
include e h p
variable (z:CatellaQ K w o d (K.c m))
local notation "Fee" Φ:max Γ:max=> listFeeQ Ω E u Φ Γ
noncomputable def listFeeQ (Ω:List (dialQ d))(E:Mark (K.c m)→ℂ)(u:C→ℝ)(X:dialQ d→C)(M:dialQ d→Family K):ℝ:= ‖E ((Ω.map M).prod m)‖ / (Ω.map (u∘ X)).prod
include hu z D
lemma pennyQ(j:Axis)(v v':ℤ)(pV: v'=v+d.val)(s j':ℤ)(r:s=v∨s=v')(r0: planeQ w o j s=Heat.gaugeShift K.B j'):
 ∃ U V:dialQ d→ Family K,
    tentPegQ w o K col mtr d (reflectQ d j v x) U ∧tentPegQ w o K col mtr d (reflectQ d j v' x) V ∧
    listFeeQ Ω E u x M^2 ≤ listFeeQ Ω E u (reflectQ d j v x) U*listFeeQ Ω E u (reflectQ d j v' x) V:=by
 -- orient first in terms of s. opposite define by not posQ s then Bend.
 let T:=reflectQ d j s x; let R(y:dialQ d):= if posQ d j s y then x (bendQ d j s y) else x y
 let i0:= posQ d j s
 let a:=mirror K j (planeQ w o j s)
 let b:= bendQ d j s
 let U(y:dialQ d):= if posQ d j s y then M y else a (M (b y))
 let V(y:dialQ d):= if posQ d j s y then a (M (b y)) else M y
 have pU:tentPegQ w o K col mtr d T U:=by
    intro y; by_cases h: posQ d j s y; · simpa only [T,U,reflectQ,if_pos h] using p y
    unfold T U reflectQ; rw [if_neg h,if_neg h]; have h0:= (p (b y)).mirrorQ j s; unfold b at h0; rw[bend_in d j s] at h0; exact h0
 have pV':tentPegQ w o K col mtr d R V:=by
    intro y; by_cases ht:posQ d j s y
    · unfold V R; rw[if_pos ht,if_pos ht]; have h0:= (p (b y)).mirrorQ j s; unfold b at h0; rw[bend_in _ j s] at h0; exact h0
    simpa only [V,R,if_neg ht] using p y
 have hp:= sameLQ l j s; let Y:=yesL Ω j s; let Z:=nonL Ω j s; obtain ⟨hv,hk⟩:= mirrorListQ l j s
 let y:=(Y.map M).prod; let r':=(Z.map M).prod
 have h1: (Ω.map M).prod=r'*y:=by rw [perm_tent e h p (permUseQ l hp),List.map_append,List.prod_append] -- careful rewrite recurrent
 have ht(y) (v:y∈ Y): posQ d j s y:=by obtain ⟨_,p⟩:=List.mem_filter.mp v; exact of_decide_eq_true p
 have h'(y)(v:y∈ Z): ¬posQ d j s y:=by obtain ⟨_,p⟩:=List.mem_filter.mp v; exact of_decide_eq_true p
 have posCost (y:dialQ d)(v:posQ d j s y)(C':dialQ d→C)(F:dialQ d→Family K)(t:tentPegQ w o K col mtr d C' F): (F y)∈Cand (K:=K) (m:=m) j j':=by
    obtain ⟨H,F',k⟩:= (t y).borrow z (e _) (h _) v
    refine ⟨aux_test F', (F'.support m).mono ?_⟩; rwa [r0] at k
 have fc (F G:Family K)(p:F∈Cand (K:=K) (m:=m) j j')(q:G∈Cand (K:=K) (m:=m) j j'): F*G∈Cand (K:=K) (m:=m) j j':= And.intro ((crownU _ _ p).1.mul (crownU _ _ q).1) ((crownU _ _ p).2.mulM (crownU _ _ q).2) -- < notation not global
 have OneQ:(1:Family K)∈Cand (K:=K) (m:=m) j j':=⟨aux_test (S:=∅) InTest.one,AtSupport.oneM _⟩
 have fuel(L:List (Family K))(h':∀ x∈L,x∈Cand (K:=K) (m:=m) j j'): L.prod∈Cand (K:=K) (m:=m) j j':=by induction L with|nil=>exact OneQ|cons u l ih=> exact fc _ _ (h' _ (by simp)) (ih (fun x v=>h' _ (by simp [v])))
 have rp (Y:List (dialQ d)):a ((Y.map M).prod)=(Y.map (a∘M)).prod:=by induction Y with|nil=>exact mirror_unit ..|cons X l ih=> simp only [List.map_cons,List.prod_cons, Function.comp_apply]; rw [show a (M X*(l.map M).prod)=a (M X)*a ((l.map M).prod) from mirror_times _ _ _,ih]
 have fy: y∈Cand (K:=K) (m:=m) j j':=fuel _ fun u v=>by obtain ⟨k,a,rfl⟩:=List.mem_map.mp v; exact posCost _ (ht _ a) _ _ p
 have qa : TestFamily K true r':=by
    suffices e:∀L:List (dialQ d),TestFamily K true ((L.map M).prod) from e Z
    intro L; induction L with|nil=>exact aux_test (S:=∅) InTest.one|cons w l ih=> exact (quals e h p _).mul ih
 have pv (x:dialQ d)(u:¬ posQ d j s x):V (b x)=a (M x):=by unfold V a b; rw [if_pos ((pos_refQ _ s j x).mpr u),bend_in d j s]
 have fr:a r'∈Cand (K:=K) (m:=m) j j':=by
    unfold r'; rw [rp]; apply fuel; intro u v; obtain ⟨k,vx,rfl⟩:=List.mem_map.mp v; unfold Function.comp; rw [←pv _ (h' _ vx)]; exact posCost _ ((pos_refQ _ s j k).mpr (h' _ vx)) _ _ pV'
 have hq:= summit D j j' (⟨a r',fr⟩:Cand (K:=K) (m:=m) j j') ⟨y,fy⟩
 change ‖Hi ((mirror K j (Heat.gaugeShift K.B j') (a r'))*y)‖^2 ≤ ‖Hi ((mirror K j (Heat.gaugeShift K.B j') (a r'))*(a r'))‖*‖Hi ((mirror K j (Heat.gaugeShift K.B j') y)*y)‖ at hq
 rw [←r0, mirror_invert K j _ qa] at hq
 have hA : (Ω.map V).prod=r'*a r':=by
    rw[perm_tent e h pV' (permUseQ l hk),List.map_append,List.prod_append,List.map_map]
    congr 1
    · exact congrArg List.prod (List.map_congr_left fun i t=>by unfold V; rw [if_neg (h' _ t)])
    rw[rp]; exact congrArg List.prod (List.map_congr_left fun i t=> pv _ (h' _ t))
 have hB:(Ω.map U).prod=a y * y:=by
    rw[perm_tent e h pU (permUseQ l hv),List.map_append,List.prod_append,List.map_map]
    congr 1
    · rw[rp]; exact congrArg List.prod (List.map_congr_left fun i t=>by unfold Function.comp U b; rw [if_neg (fun v=> (pos_refQ _ s j i).mp v (ht _ t)),bend_in d j s i])
    exact congrArg List.prod (List.map_congr_left fun i t=>by unfold U; rw [if_pos (ht _ t)])
 have px:(Ω.map (u∘ x)).prod= (Z.map (u∘ x)).prod*(Y.map (u∘x)).prod:=by rw [((permUseQ l hp).map (u∘x)).prod_eq, List.map_append,List.prod_append]
 have pt:(Ω.map (u∘ T)).prod=(Y.map (u∘ x)).prod^2:=by
    rw[((permUseQ l hv).map (u∘T)).prod_eq,List.map_append,List.prod_append,List.map_map,sq]; congr 1
    · exact congrArg List.prod (List.map_congr_left fun i t=>by unfold Function.comp T reflectQ; rw[if_neg (fun v=> (pos_refQ _ s j i).mp v (ht _ t)), bend_in d j s i])
    exact congrArg List.prod (List.map_congr_left fun i t=>by unfold Function.comp T reflectQ; rw [if_pos (ht _ t)])
 have pr:(Ω.map (u∘R)).prod=(Z.map (u∘x)).prod^2:=by
    rw [((permUseQ l hk).map (u∘R)).prod_eq,List.map_append,List.prod_append,List.map_map,sq]; congr 1
    · exact congrArg List.prod (List.map_congr_left fun i t=>by unfold Function.comp R; rw [if_neg (h' _ t)])
    exact congrArg List.prod (List.map_congr_left fun i t=>by unfold Function.comp R; rw[if_pos ((pos_refQ d s j i).mpr (h' _ t)),bend_in d j s i])
 have fee0:listFeeQ Ω E u x M^2≤ listFeeQ Ω E u R V * listFeeQ Ω E u T U:=by
    unfold listFeeQ; rw [pr,hA,pt,hB, h1,px, div_pow,mul_pow,div_mul_div_comm]
    apply div_le_div_of_nonneg_right hq; positivity
 subst v'; rcases r with t|t <;> subst s
 · have he:R=reflectQ d j (v+d.val) x:= funext fun i=>by unfold R reflectQ; rw[pos_backQ d v j i,rev_backQ d v j]; by_cases h:posQ d j v i <;> simp [h]
   refine ⟨U,V,pU,he ▸ pV',?_⟩; rw [←he,mul_comm]; exact fee0
 have he:R=reflectQ d j v x:=funext fun i=>by unfold R reflectQ; rw [pos_backQ d v j i, rev_backQ d v j]; by_cases h:posQ d j v i <;> simp [h] -- wait R when pos s then x (b y), else x: pos s=¬pos v. Thus R=x if pos v. yes.
 exact ⟨V,U,he ▸ pV',pU,he ▸ fee0⟩
#check Cand
#print axioms pennyQ
end WallsQ
end YM.CF.Buffered.Afterglow.Tower.SlabMark
end
