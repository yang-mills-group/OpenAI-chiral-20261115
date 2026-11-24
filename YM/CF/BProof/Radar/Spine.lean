import YM.CF.BProof.Radar.Dig
/- net toolbox, uniformly in n. proximity multiplier K chosen + station bill no details omitted. -/
set_option synthInstance.maxSize 4096
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 5000
set_option maxHeartbeats 650000
noncomputable section
namespace YM.CF.BProof.Mesh
open Lattice Function Finset Equiv Regard Rows
open scoped BigOperators Classical
variable {C A:Type*}{n:Side}{s z l k:ℕ}
open Sleet Policy Crop.Native
abbrev tollK (l:ℕ)(K:ℕ) := (2 + 2*stage0 l) + (2*stage0 (stage0 (K*l))) -- tune 2*2*k*...
abbrev Board (n:Side)(l K:ℕ) := Earsa l n× Veep (K*l) n
abbrev partK(K:ℕ):=(shell K).card+1
def colours(n:Side)(l K:ℕ):Field n (Board n l K) (Fin (partK K)) := Busy.grant (fun x=>Hop l n x.1) (fun x=>(marked (many (K*l) n)) x.2) (K*l) (partK K -1) (Syr (K*l)) -- tune definitional reduction
abbrev netW (n:Side)(l k:ℕ):Field n (Board n l k) Prop:=fun x i=> Hop l n x.1 i
abbrev Earning(n:Side)(l k:ℕ) := Joint (netW n l k) (fun i=>Mesh.marked (many (k*l) n) i.2)
local notation "ψ"=> Earning n
abbrev asset(l K:ℕ) := let t:= K*l; (Syr t*t)+(pay_l l+(0+majesty t+0))+ (Syr t*t)
variable (h:tollK l k ≤ n.val) -- must strict for stage0 maybe second compare off by2
include h
lemma enroll1 : 2*stage0 l< n.val:= by unfold tollK at h; omega
lemma enroll2 : 2*stage0 (stage0 (k*l))< n.val:=by unfold tollK at h; omega
instance :Finite (Board n l k):= by unfold Board; infer_instance -- maybe hb stuck Together
lemma wear0 : Nonempty (Board n l k):=by
 let t:= enroll1 h; let v:=enroll2 h; have V:= (pity _ _ v).1; have U:Nonempty (Earsa l n):=(haveH n l t).1; exact ⟨U.some,V.some⟩ -- tune
lemma ready : SplitK n (ψ l k) (pay_l l+(0+majesty (k*l)+0))∧Spotty (netW n l k) l (cover l) ∧ OrderC (fun i:Board n l k=>(marked (many (k*l) n)) i.2) (k*l) ∧ Sym (ψ l k):=by
 obtain ⟨-,g,H,U⟩:= pity _ _ (enroll2 h); obtain ⟨-,u,v,p⟩:=haveH n l (enroll1 h); let K:=Syr (k*l)
 exact ⟨SplitK.product (u.star (by omega)) ((Uses.epoch (l:=0) (aware0 _) U).star (by omega)),fun x=>p x.1, fun x y u v w=> order0 g x y u v w.2, v.prod (sym0 _ H)⟩
structure Bill (n:Side)(l k:ℕ){V:Type*}(X:Field n A Prop)(U:Field n A V) :Prop where
 coat : Nonempty A
 inK : Sym (Joint X U)
 separated : SplitK n (Joint X U) (asset l k)
 pack : Spotty X l (cover l)
 safe : Busy.goodHue X U (k*l)
lemma palette (u:0<l): Bill n l k (netW n l k) (colours n l k):=by
 obtain ⟨V', Hp, p, v⟩:=ready h; let l':= k*l; let p':= Syr l'; let X:=netW n l k; let Y:=fun i:Board n l k=>(marked (many (k*l) n)) i.2; let Ω:= Joint X Y; have he: Loyal Ω (Joint X (colours n l k)):= Mesh.Loyal.meet (day ..).1 (Busy.home X Y _ _ _); have hv: Uses Ω (Joint X (colours n l k)) (p'*l'):= Mesh.Uses.comm (dawn ..).1 (Busy.grantD X Y _ _ _)
 refine ⟨wear0 h, he.keep v, hv.epoch V', Hp, Busy.leased p (fun i y=>position _ k l (Hp i).1 u _)⟩
end YM.CF.BProof.Mesh
