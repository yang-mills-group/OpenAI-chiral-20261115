import YM.CF.Emu.Fez
/-!
Algebraic factor license on Wake clam formulas at *any* size.
Use only in limits with all crossed covariance entries tending to zero.
Offer in reading order. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
namespace YM.CF.WakeInvestment
open Fock Emu Function Filter Metric NormedSpace
open scoped Topology BigOperators
variable {α β : Type*} (D G:α→α→ℂ)(L W:List α) (v:Cl α)
private lemma val_cite (x:α)(v:Cl α)(g:Bout α): offer D (cites x v g)= (cval g.neg * D x g.front)*offer D v:=by simp only [offer,cites,cxor,List.map_cons,List.prod_cons]; ring
private lemma val_stat (x:α)(v:Cl α): offer D (extendsU x v) = offer D v:=rfl
private lemma picks_join {z:Bout α}{l:List α}{x:α}(p:z∈ picks l) : x ∈ l ↔ x=z.front ∨ x∈ z.back:= by
 induction l generalizing z with
 | nil=> simp [picks] at p
 | cons i l ih=>
    rcases List.mem_cons.mp p with p|h; · rw [p]; exact List.mem_cons
    obtain ⟨z,p',rfl⟩:= List.mem_map.mp h; rw [List.mem_cons,ih p']; unfold beside; dsimp only; rw [List.mem_cons]; tauto

private def tally (l:List β)(d:β→ℂ):ℂ:=(l.map d).sum
private lemma tnil (f:β→ℂ): tally [] f=0:=rfl
private lemma tcons (a:β)(l:List β)(f:β→ℂ): tally (a::l) f=f a+tally l f:=rfl
private lemma tsame (l:List β)(p q:β→ℂ)(h:∀ i∈l,p i=q i): tally l p=tally l q:=by induction l with|nil=>rfl|cons i l ih=> rw [tcons,tcons,h _ List.mem_cons_self,ih fun i g=> h i (List.mem_cons_of_mem _ g)]
private lemma tzero (l:List β)(f:β→ℂ) (p:∀ i∈l,f i=0) : tally l f=0:=by induction l with|nil=>rfl|cons i l ih=> rw [tcons,p _ List.mem_cons_self, ih fun i h=>p i (List.mem_cons_of_mem _ h),add_zero]
private lemma tref (l:List β)(g:ℂ)(f:β→ℂ):tally l (fun i=> g*f i)=g*tally l f:=by induction l with|nil=>rw [tnil,tnil,mul_zero]|cons i l ih=> rw [tcons,tcons,ih,mul_add]
private lemma tsch (l:List β)(f:β→List α)(g:α→ℂ): tally (l.flatMap f) g=tally l (fun i=> tally (f i) g):=by
 induction l with|nil=>rfl|cons i l ih=> rw [List.flatMap_cons,tcons]; unfold tally at *; rw [List.map_append,List.sum_append,ih]
-- Fold states starting with right text. Need consistency with claps.
private def adjure (L:List α)(F: Cl α→ℂ): Cl α→ℂ:= fun v=> L.reverse.foldr (fun i f w=> tally (besideX i w) f) F v
private lemma adj_nil (F:Cl α→ℂ): adjure [] F=F:=rfl
private lemma adj_more (L:List α)(i:α)(F:Cl α→ℂ): adjure (i::L) F=adjure L (fun w=>tally (besideX i w) F):=by unfold adjure; rw [List.reverse_cons,List.foldr_append]; rfl
private lemma adj_p (L:List α)(i:α)(F:Cl α→ℂ)(v:Cl α) : adjure (L++[i]) F v=tally (besideX i v) (adjure L F):=by unfold adjure; rw [List.reverse_append]; rfl
private lemma adj_bill (F:Cl α→ℂ): tally (claps (L++W)) F=tally (claps W) (adjure L F):=by
 induction L generalizing F with
 | nil=> rw [List.nil_append,adj_nil]
 | cons i L ih=> rw [List.cons_append,claps,tsch,adj_more]; exact ih _
private def initC (α:Type*) : Cl α:=⟨false,[],[]⟩
private lemma budget_release : runes D L=adjure L (spinC D) (initC α):=by change tally _ _=_; have hp:= adj_bill L [] (spinC D); rw [List.append_nil,claps,tcons,tnil,add_zero] at hp; exact hp  -- claps unfold

-- prove decomposed residual-state bill. use recurWitness by reverse.
private def walker (D:α→α→ℂ)(L M:List α):ℂ:= adjure L (spinC D) ⟨false, [], M⟩
private lemma adj_one (i:α)(f:Cl α→ℂ)(w:Cl α): tally (besideX i w) f=f (extendsU i w)+tally (picks w.term) (fun g=> f (cites i w g)):=by unfold besideX; rw [tcons]; unfold tally; rw [List.map_map]; rfl
private lemma simpler (a:ℕ)(W:List α)(h:W.length≤a): ∀ v:Cl α, adjure W (spinC D) v=offer D v * walker D W v.term := by
 induction a generalizing W with
 | zero=> simp at h; intro v; subst W; rw [adj_nil,spinC,walker,adj_nil,spinC]; split <;> simp [offer,cval, *] -- causes reduction offer?
 | succ a ih=>
    cases W using List.reverseRecOn with
    | nil=> intro v; rw [adj_nil,spinC,walker,adj_nil,spinC]; split<;> simp [offer,cval, *]
    | append_singleton W i =>
       have hx:W.length≤a:= Nat.le_of_succ_le_succ (by simpa using h); intro v; let y:Cl α:= ⟨false,[],v.term⟩; let f:=adjure W (spinC D)
       unfold walker; rw [adj_p,adj_p,adj_one,adj_one]; simp_rw [ih W hx,val_stat,val_cite] -- oops valstat target y ok unfolding
       simp only [show offer D {cpos:=false,up:=[],term:=v.term}=1 from by simp [offer,cval],one_mul,mul_one]; rw [mul_add,←tref]; refine congrArg₂ (·+·) rfl (tsame _ _ _ fun i _=>?_); simp only [cites]; ring
private lemma dirty (P:α→Prop)(X:Cl α)(p:∃ g∈X.term,P g)(u:∀ i∈L,∀ y,P y→D i y=0) : adjure L (spinC D) X=0:=by
 induction L using List.reverseRecOn generalizing X with
 | nil=>
    rw [adj_nil]; rcases p with ⟨g,p,_⟩; unfold spinC; cases h:X.term; · simp [h] at p
    rfl
 | append_singleton L i ih=>
    obtain ⟨g,p,h⟩:=p; have hv:∀ j∈L,∀ y,P y→D j y=0:=fun j k=>u j (List.mem_append_left _ k); rw [adj_p,adj_one]; rw [ih (extendsU i X) ⟨g,List.mem_cons_of_mem _ p,h⟩ hv, tzero]; swap
    · intro z f; rcases (picks_join f).mp p with p|p
      · rw [simpler D L.length L le_rfl,val_cite, u _ (List.mem_append_right _ List.mem_cons_self) _ (p ▸ h)]; ring
      exact ih _ ⟨_,p,h⟩ hv
    rw [add_zero]
lemma rune_divide (p:∀ i∈L,∀ j∈W,D i j=0) : runes D (L++W)=runes D L*runes D W:=by
 have he {L:List α}{z:Cl α}(v:z∈claps L)(i:α)(h:i∈z.term): i∈L:=by
    induction L generalizing z with
    |nil=>rw [show z=initC α from List.mem_singleton.mp v] at h; exact (List.not_mem_nil h).elim
    |cons x L ih=>
      obtain ⟨a,p,v⟩:=List.mem_flatMap.mp v; rcases List.mem_cons.mp v with v|u
      · rw [v] at h; exact List.mem_cons.mpr ((List.mem_cons.mp h).imp id fun i=> ih p i)
      obtain ⟨g,v',rfl⟩:= List.mem_map.mp u; exact List.mem_cons_of_mem _ (ih p ((picks_join v').2 (Or.inr h)))
 change tally _ _=_* tally _ _; rw [adj_bill,←tref]; apply tsame; intro i v
 by_cases e:i.term=[]
 · rw [simpler D L.length L le_rfl,e,budget_release];-- remove
   simp only [spinC,e,List.isEmpty_nil,ite_true]; change offer D i*walker D L _= walker D L _*_; rw [mul_comm]
 have h:∃ j∈ i.term,j∈W:= by obtain ⟨j,t⟩:= List.exists_mem_of_ne_nil _ e; exact ⟨j,t,he v _ t⟩
 rw [dirty D L (fun i=> i∈W) i h p]; simp [spinC,e] -- `e`

private def boutMap (f:α→ β)(z:Bout α):Bout β:=⟨z.neg,f z.front,z.back.map f⟩
private def clMap (f:α→ β)(z:Cl α):Cl β:=⟨z.cpos,z.up.map (fun i=>(f i.1,f i.2)),z.term.map f⟩
private lemma picks_map (f:α→β)(L:List α): picks (L.map f)= (picks L).map (boutMap f):=by
 induction L with|nil=>rfl|cons i L ih=> rw [List.map_cons,picks,picks,ih]; simp only [List.map_map,List.map_cons]; rfl
private lemma claps_map (f:α→β)(L:List α):claps (L.map f)= (claps L).map (clMap f):=by
 have he(i:α)(u:Cl α): besideX (f i) (clMap f u)=(besideX i u).map (clMap f):=by unfold besideX; rw [clMap,picks_map]; simp only [List.map_map,List.map_cons]; rfl
 induction L with|nil=>rfl|cons i L ih=> rw [List.map_cons,claps,ih,claps,List.flatMap_map,List.map_flatMap]; congr 1; exact funext (he i)
lemma rune_map (f:α→β)(G:β→β→ℂ)(h:∀ i j,D i j= G (f i) (f j)): runes G (L.map f)=runes D L:=by
 unfold runes; rw [claps_map,List.map_map]
 congr 2
 funext i; change spinC G (clMap f i) = _; simp only [spinC,clMap, List.isEmpty_map, h, offer,List.map_map,Function.comp_def]
#print axioms rune_divide
#print axioms rune_map
end YM.CF.WakeInvestment
