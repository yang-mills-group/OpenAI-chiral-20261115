import YM.SU5.FiniteGaugeData.Maypole.Folio
/-! # Long gaps. Eu point operations, joins and priced measures -/
set_option autoImplicit false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Mink General Lorentz Complex
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
open Poin Celeritas Land Leal Breve Poin.Gem
open Boundary Probe
namespace Folio
variable {H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(Ω:H)(hp:∀ x:E4,M S x Ω=Ω)
-- chronology.Braces
variable {α:Type}(A:α→H.Op)(ν:α→ℕ)
local notation "Ι"=> Item α
local notation "Ω°"=> wordValue S Ω A ν
local notation "Φ"=> legis S A ν
local notation "δ"=> gapK S ν
local notation "η"=> timesA a
local notation "Γ"=> leanX S
section
variable (p:E4)(L L':List (Item α))
abbrev shift(p:E4)(x:Ι):Ι:=(x.1,p+x.2)
abbrev shifted(p:E4)(L:List (Item α)):= L.map (shift p)
local notation "z'"=> SEP a p
lemma stamp_z (x:Ι): stamps S A (shift p x)= optx S (stamps S A x) ((SEP a p).val):=by unfold stamps coreSp; rw [opt_act]; change optx S (A x.1) _=_; rw [shift,show SEP a (p+x.2)= _ from (map_add ..:SEP a (p+x.2)= SEP a p+SEP a x.2)]; rfl -- tune
@[simp] lemma gap_z(x y:Ι): gapK S ν (shift p x) (shift p y)=gapK S ν x y:=by simp [gapK]
lemma travel (x:E4)(X Y:H.Op): optx S (X*Y) x=optx S X x*optx S Y x:=by
 let F:=M S x; let f:=M S (-x); have he:f*F=1:=(tgo S (-x) x).trans (show M S (-x+x)=1 from (by rw [neg_add_cancel,tini]))
 change F*(X*Y)*f=F*X*f*(F*Y*f); rw [mul_assoc (F*X) f, ←mul_assoc f (F*Y),←mul_assoc f F,he]; simp only [one_mul,mul_assoc]
lemma law_unit(x:E4): optx S 1 x=1:=by rw [optx,mul_one,tgo,add_neg_cancel,tini]
lemma respire (k:ahead a L): legis S A ν (shifted p L)= optx S (legis S A ν L) (SEP a p).val:=by
 cases L with| nil=> exact (law_unit S _).symm | cons x L=>
 induction L generalizing x with
 | nil=> change Φ [shift p x] = _; rw [show Φ _=_ from solitary _ (δ) _,show Φ [x]=_ from solitary ..,stamp_z]
 | cons v l ih=>
    obtain ⟨k,h⟩:=List.pairwise_cons.mp k; let T:=(z').val; let u:=v.2 a-x.2 a; let F:= δ x v; have he:0<u:= sub_pos.mpr (k v List.mem_cons_self); have hh:optx S F T=F:=by
       have hx:Commute (M S T) F:= (mslot S T (OS.Semigroup.duration u.toNNReal) (dur.mpr (Real.toNNReal_pos.mpr he)) (ν x.1+ν v.1)).symm; unfold optx; rw [hx.eq,mul_assoc, tgo,add_neg_cancel,tini,mul_one]
    change Φ (shift p x::shift p v::shifted p l)= _; unfold legis; rw [twoF,twoF, gap_z,stamp_z, show Film (stamps S A) _ (shift p v::shifted p l) = _ from ih v h,travel S T (stamps S A x*F) (Φ (v::l)), travel S T (stamps S A x) F, show optx S (δ x v) T=F from hh]
lemma coreComm (X:H.Op): optx S X ((SEP a p).val)* S.U (SEP a p)= S.U (SEP a p)*X:=by
 let v:=(z').val; rw [←laneslot,optx, mul_assoc (M S v*X),tgo,neg_add_cancel,tini,mul_one]
lemma awakens (h:ahead a L): ahead a (shifted p L):=by
 refine List.pairwise_map.mpr (h.imp ?_); intro x y h; simp [timesA]; exact h
lemma aheadJoin (h:0≤p a)(k:BackE a 0 L)(g:LaneE a 0 L'): ahead a (L++shifted p L'):= by
 refine List.pairwise_append.mpr ⟨k.1,awakens p L' g.1,?_⟩; intro x e'b y t; obtain ⟨z,u,rfl⟩:= List.mem_map.mp t; apply lt_trans (k.2 x e'b); change 0<(p+z.2) a; simpa using add_pos_of_nonneg_of_pos h (g.2 z u) -- may need
include hp
lemma originIn (h:ahead a L): wordValue S Ω A ν (shifted p L)= wordValue S Ω A ν L:=by rw [wordValue,respire _ _ _ _ _ h]; change inner ℂ Ω (M S _ (Φ L (M S _ Ω)))=_; rw [tboth,hp]
-- composition with cross.Time equality originally no rotation.P
private lemma fusing(t w:Ι)(Y W:List Ι)(u:0≤p a)(ht: timesA a t<0)(hw:0< timesA a w) (L':ahead a (w::W)):inner ℂ (role S Ω A ν 0 (Y++[t])) ((S.E (p a).toNNReal*S.U (SEP a p)) (face S Ω A ν 0 (w::W)))= wordValue S Ω A ν ((Y++[t]) ++ shifted p (w::W)):=by
 let Wq:= SEP a p; let Q:= S.U Wq; let xp:= (p a).toNNReal; let X:= S.E xp; let T:= Front S A ν 0 (w::W); let E:=Back S A ν 0 (Y++[t]); let L:= shifted p (w::W)
 have H:0< 0-timesA a t:=sub_pos.mpr ht; have pW:0<timesA a w-0:=sub_pos.mpr hw; let q:=Γ (0-η t) (ν t.1); let u':=Γ (η w-0) (ν w.1);
 have he: E* (X*Q)*T=Φ ((Y++[t])++L)*Q :=by
    have hT:T=u'* Φ (w::W):=by unfold T u' Front; rw [budgetFoot,zero_add]
    have hE:E= Φ (Y++[t])*q:=by unfold E Back q; rw [budgetBack,add_zero]
    have hx: q*X*u'=δ t (shift p w):=by rw [show q*X*u'= _ from invest (n:=ν t.1) (k:=ν w.1) S H u pW]; unfold gapK; change leanX S _ _=leanX S ((p+w.2) a-t.2 a) _; congr 1; rw [PiLp.add_apply]; unfold timesA; ring
    have ht:Q*Φ (w::W)=Φ L*Q:=by rw [show Φ L=_ from respire S A ν p (w::W) L',coreComm]; -- maybe coreComm rw specify
    rw [show Φ ((Y++[t])++L)=Φ (Y++[t])*δ t (shift p w)*Φ L from joiningF (stamps S A) (δ) Y (shifted p W) _ _,hT,hE, ←hx, mul_assoc]; simp only [mul_assoc]; rw [←mul_assoc Q u',(comm_u S Wq (timesA a w-0) pW).eq.symm,mul_assoc u' Q, ht]
 change inner ℂ (E.adjoint Ω) _=_; rw [ContinuousLinearMap.adjoint_inner_left]; refine congrArg _ ( (DFunLike.congr_fun he Ω).trans (congrArg (fun x=> (Φ ((Y++[t])++L)) x) (offer S Ω hp Wq)))
lemma rho_join (u:0≤p a)(h:BackE a 0 L)(k:LaneE a 0 L') : inner ℂ (role S Ω A ν 0 L) ((S.E (p a).toNNReal*S.U (SEP a p)) (face S Ω A ν 0 L'))= wordValue S Ω A ν (L ++ shifted p L'):= by
 let T:= S.E (p a).toNNReal; let W:=S.U (z'); let R₀:= T*W; have hz: R₀ Ω=Ω:=(congrArg T (offer S Ω hp _)).trans (shed S Ω hp _); have hs:star R₀ Ω=Ω:=by unfold R₀ W T; rw [star_mul,← laneslot, tstar,heat_a]; exact (congrArg _ (shed S Ω hp _)).trans (hp _)
 cases pA:L.reverse with
 | nil=>
    rw [List.reverse_eq_nil_iff.mp pA,List.nil_append,originIn S Ω hp A ν p L' k.1]; let X:=face S Ω A ν 0 L'; change inner ℂ (star (Φ [] * (1:H.Op)) Ω) (R₀ X)=_; rw [show Φ []=1 from rfl,mul_one,star_one]; change inner ℂ Ω (R₀ X)=_; rw [show inner ℂ Ω (R₀ X)=inner ℂ (star R₀ Ω) X from (ContinuousLinearMap.adjoint_inner_left ..).symm,hs]
    have hw: star (billBefore S ν 0 0 L') Ω=Ω:=by cases L' with| nil=> rw [billBefore,star_one]; rfl| cons l A=> rw [budgetFoot,warm_a]; exact earnO S Ω hp _ (sub_pos.mpr (k.2 l List.mem_cons_self)); exact sub_pos.mpr (k.2 l List.mem_cons_self)
    change inner ℂ Ω (billBefore S ν 0 0 L' (Φ L' Ω))=_; rw [←ContinuousLinearMap.adjoint_inner_left]; rw [show (billBefore S ν 0 0 L').adjoint Ω=Ω from hw]
 | cons l V=>
    have hv:L= V.reverse++[l]:=by nth_rw 1 [← List.reverse_reverse L,pA,List.reverse_cons]
    rw [hv] at h ⊢; have he:=h.2 l (by simp); cases L' with
    | cons t M=> exact fusing S Ω hp A ν p l t _ M u he (k.2 t List.mem_cons_self) k.1
    | nil=>
       rw [show shifted p ([]:List (Item α))=[] from rfl,List.append_nil]; change inner ℂ ((Back S A ν 0 _).adjoint Ω) (R₀ ((billBefore S ν 0 0 []) ((Φ []) Ω)))=_; rw [billBefore, show Φ []=1 from rfl]; change inner ℂ ((Back S A ν 0 _).adjoint Ω) (R₀ Ω)=_; rw [hz,ContinuousLinearMap.adjoint_inner_left]; unfold Back; rw [budgetBack]; exact congrArg (inner ℂ Ω) (congrArg ((Φ (V.reverse++[l])).toLinearMap) (earnO S Ω hp _ (n:=ν l.1+0) (sub_pos.mpr he)))
end
end Folio
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp
