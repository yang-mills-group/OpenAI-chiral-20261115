import YM.CF.Vault.Picket
import YM.CF.Paige.Vacate
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vault
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip Scroll Branch Paige
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8000
variable {N P L:Side}{ho:Odd L.val}{j n l:ℕ}(e:Even j)(p:1≤j)
variable (T:Tollage j L ho n l)(G: Ratio N P)(he:G.count=L)(x:Sew N P)
variable {u r:Bool}(a:Shape)(Y:ColorT u)(V:UNI SpinIdx)(h:JetS a.s u r V)
lemma guild {k:ℝ}(v:Gild G x k): Gild G (lotX G a Y x) k:= by
 obtain ⟨p,h,u,w⟩:= v; refine ⟨alongS Y a G x.1 k p, swayX (N:=P) Y _ _ _ _ h,swayX Y _ _ _ _ u,?_⟩
 intro i; rw [←dist_eq_norm]; change dist (Y.X (x.2.1 _)) (Y.X (x.2.2 _))< k; rw [IsometryEquiv.dist_eq,← Shape.foldsT]; exact (by rw [Subtype.dist_eq,dist_eq_norm]; exact w _)
def terms (b:Bool)(j:ℕ)(L:Side)(ho:Odd L.val)(n:ℕ)(M:Male){N P:Side}(G: Ratio N P) (x:Sew N P):ℂ:=beard (foal j b M G (unionP x.1)) (wh j L ho b M G (unionP x.1)) (ticketT (@Peaks.cloth j) b M G (unionP x.1)) (dotB true G x) (dotB false G x) n
def lots (b:Bool)(j l:ℕ)(M:Male){N P:Side}(G:Ratio N P) (x:Sew N P):ℂ:=beard (lobe G b) (lobe G b) (ticketT (@Peaks.cloth j) b M G (unionP x.1)) (dotB true G x) (dotB false G x) l
abbrev SpanX (j:ℕ)(L:Side)(ho:Odd L.val) (M:Male) {N P:Side}(G:Ratio N P)(x:Sew N P): Prop:= Along j L ho (@Peaks.cloth j) true M G (unionP x.1)
lemma age_val (M:Male)(b:Bool)(A:SpanX j L ho M G x): let v:=(M,noneL);
 chalk j b v G (post x)=mateF (foal j b) M G (post x) ∧ umber j L ho b v G (post x)=mateF (wh j L ho b) M G (post x):=by
 intro v; have he:chalk j true v G (post x)=coast j M G (post x):=paddle_serene _ _ _ _ _ A.lead -- tune
 have hx:umber j L ho true v G (post x)=urban j L ho M G (post x):=paddle_serene _ _ _ _ _ A.beam
 cases b; swap; exact ⟨he,hx⟩
 change 1 - chalk j true v G _= _ ∧ 1-umber j L ho true v G _=_; rw [he,hx]; exact ⟨(foil_neg j G true M (unionP x.1)).symm,(wh_neg j L ho G true M (unionP x.1)).symm⟩
lemma turn_pt (M:Male)(b:Bool)(A:SpanX j L ho M G x) : fineT j L ho b n l G x (M,noneL)=terms b j L ho n M G x∧ priceT j b l G x (M,noneL)=lots b j l M G x :=by
 unfold fineT priceT; dsimp only; rw [(age_val G x M b A).1,(age_val G x M b A).2,fadesZero]; exact ⟨rfl,rfl⟩
include T he
abbrev hireT(j:ℕ)(L:Side)(ho:Odd L.val)(n k:ℕ)(M:Male){N P:Side}(G:Ratio N P)(x:Sew N P):ℂ:= (cExp j L ho (@Peaks.cloth j) n M G (post x)).trace - (eExp (@Peaks.cloth j) k M G (post x)).trace
abbrev poised (b:Bool)(x:Sew N P)(M:Male) := train (foal j b M G (unionP x.1)) (wh j L ho b M G (unionP x.1)) (ticketT (@Peaks.cloth j) b M G (unionP x.1)) (dotB true G x) (dotB false G x) -- params? note T etc implicitly
lemma flare (M:Male)(A:SpanX j L ho M G x)(u:Tollday j L ho n l x G) : terms false j L ho n M G x-lots false j l M G x=star (terms true j L ho n M G x-lots true j l M G x):=by
 obtain ⟨a,b⟩:= turn_pt (n:=n ) (l:=l) G x M false A; obtain ⟨q,r⟩:= turn_pt (n:=n ) (l:=l) G x M true A; rw [←a,←b,←q,←r]; exact pairedLog T G he x u M
variable {k:ℝ}(hk:JointB G x.1 k)(hc:∀ x:Bkg (More N),Guard x k→PaidG j k x)(hg:∀ x:Bkg (More P),Guard x k→ PaidG j k x)(A:Tollday j L ho n l x G)
include p hk hc hg A h
lemma clap (b:Bool)(M:Male)(Z:SpanX j L ho M G x): let y:=lotX G a Y x;
 terms (r.xor b) j L ho n M G y = cSignX u (terms b j L ho n M G x) ∧ lots (r.xor b) j l M G y=cSignX u (lots b j l M G x):=by
 subst L; set i:=(M,noneL)
 intro y; obtain ⟨B,U⟩:=hoarD G ho a Y V h j p M k x.1 hk hc hg b
 let C:= pflux a G V Y; let F:=dotB true G x; let D:=dotB false G x
 let L:= fade j b i G (post x); have hK:L=ticketT (@Peaks.cloth j) b M G (unionP x.1):= fadesZero ..
 obtain ⟨k1,k2,k3,k4⟩:= A i; obtain ⟨hw,hx⟩:= (k4 b).2
 have ht:=titles G ho a Y V h j M x.1 b ((dusk_eq G j M x) ▸ k3 : IsUnit (Peaks.cloth j M G (unionP x.1)))
 have ht':congrC C (windX u F.val)=(dotB true G y).val:=tyL G ho a Y V h true x
 have hp:congrC C (windX u D.val)=(dotB false G y).val:=tyL G ho a Y V h false x
 let H:=foal j b M G (unionP x.1); let S:=wh j G.count ho b M G (unionP x.1)
 obtain ⟨h1,h2⟩:=age_val G x M b Z; change chalk j b i G _=H at h1; change umber j G.count ho b i G _=S at h2
 change Stay _ (train (chalk j b i G _) (umber j G.count ho b i G _) L F D) n at hw; change Stay _ (train (lobe G b) (lobe G b) L F D) _ at hx
 rw [h1,h2,hK] at hw; rw [hK] at hx
 unfold terms lots
 constructor
 · have hv:=glide_k _ H S _ _ _ u C hw; rw [show sings u C H=_ from B,show sings u C S=_ from U,show sings u C _=_ from ht,ht',hp] at hv; exact hv
 have hv:=glide_k _ _ _ _ _ _ u C hx; rw [show sings u C (lobe G b)=_ from taxL _ a Y V h b,show sings u C _=_ from ht,ht',hp] at hv; exact hv
lemma stand_roar (M:Male)(Z:SpanX j L ho M G x) : let y:=lotX G a Y x; terms true j L ho n M G y-lots true j l M G y= cSignX (u.xor r) (terms true j L ho n M G x-lots true j l M G x):=by
 let X:= (fun b=> clap p T G he x a Y V h hk hc hg A b M Z); intro y; cases r; swap
 · obtain ⟨B,W⟩:= X false; change terms true _ _ _ _ _ _ y=_ at B; change lots true _ _ _ _ y=_ at W; rw [B,W]
   rw [← show ∀ a c,cSignX u (a-c)=cSignX u a-cSignX u c from fun a c=>by cases u <;>simp [cSignX]]; rw [flare T G he x M Z A]; cases u <;> simp [cSignX]
 obtain ⟨A,B⟩:= X true; change terms _ _ _ _ _ _ G y=_ at A; change lots _ _ _ _ G y=_ at B; simp only [Bool.false_xor] at A B; rw [A,B]; cases u<;>simp [cSignX]
end YM.CF.Vault
