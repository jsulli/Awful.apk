package com.ferg.awfulapp.popupmenu;

import android.os.Bundle;
import android.support.annotation.NonNull;
import android.support.annotation.Nullable;
import android.support.v4.app.DialogFragment;
import android.support.v7.widget.LinearLayoutManager;
import android.support.v7.widget.RecyclerView;
import android.text.method.ScrollingMovementMethod;
import android.view.LayoutInflater;
import android.view.View;
import android.view.ViewGroup;
import android.widget.ImageView;
import android.widget.TextView;

import com.ferg.awfulapp.R;
import com.ferg.awfulapp.provider.ColorProvider;

import java.util.List;

import butterknife.BindView;
import butterknife.ButterKnife;

import static butterknife.ButterKnife.findById;

/**
 * Created by baka kaba on 22/05/2017.
 * <p>
 * A menu dialog that displays a list of actions.
 * <p>
 * Subclass this and implement the methods that provide a list of actions, and handle when the user
 * clicks one of them. I recommend following the approach in {@link UrlContextMenu}, where you define
 * the menu items as an enum, add whichever items you need, and switch on the enum cases to handle
 * the user's selection. Just pass the enum as the type parameter for the class.
 */
public abstract class BasePopupMenu<T extends AwfulAction> extends DialogFragment {

    int layoutResId = R.layout.select_url_action_dialog;

    private List<T> menuItems = null;

    BasePopupMenu() {
        this.setStyle(DialogFragment.STYLE_NO_TITLE, 0);
    }

    @Override
    public void onCreate(@Nullable Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        init(getArguments());
        menuItems = generateMenuItems();
    }

    @Override
    public View onCreateView(LayoutInflater inflater, ViewGroup container, Bundle savedInstanceState) {
        final View result = inflater.inflate(layoutResId, container, false);
        ButterKnife.bind(this, result);

        TextView actionTitle = findById(result, R.id.actionTitle);
        actionTitle.setMovementMethod(new ScrollingMovementMethod());
        actionTitle.setText(getTitle());

        RecyclerView actionsView = findById(result, R.id.post_actions);
        actionsView.setAdapter(new ActionHolderAdapter());
        actionsView.setLayoutManager(new LinearLayoutManager(getContext()));

        getDialog().setCanceledOnTouchOutside(true);
        return result;
    }


    /**
     * Called during onCreate, passing in the arguments set with {@link android.support.v4.app.Fragment#setArguments(Bundle)}.
     * <p>
     * Fragments can be recreated, losing all their state, so set the arguments when creating a new
     * fragment instance, and unpack them and build your state here.
     */
    abstract void init(@NonNull Bundle args);


    /**
     * Generate the list of menu items to display.
     * <p>
     * This is where you should define the items you need to include, in the order they should be displayed.
     *
     * @return the list of menu items, in order
     */
    @NonNull
    abstract List<T> generateMenuItems();

    /**
     * The title to display on the dialog.
     */
    @NonNull
    abstract String getTitle();

    /**
     * Called when the user selects one of your menu items.
     *
     * The dialog is dismissed after this method is called - don't dismiss it yourself!
     */
    abstract void onActionClicked(@NonNull T action);

    /**
     * Get the text to display for a given action.
     * <p>
     * The default implementation just defers to the action's own {@link AwfulAction#getMenuLabel()} method.
     * You can override this if you need to manipulate the text, e.g. if you've defined a format string
     * for a particular item, and you need to pass in the specific parameters for this menu instance.
     *
     * @param action the action item being displayed
     */
    @NonNull
    String getMenuLabel(@NonNull T action) {
        return action.getMenuLabel();
    }


    class ActionHolder extends RecyclerView.ViewHolder {
        @BindView(R.id.actionTag)
        ImageView actionTag;
        @BindView(R.id.actionTitle)
        TextView actionText;

        ActionHolder(View view) {
            super(view);
            ButterKnife.bind(this, view);
        }
    }

    private class ActionHolderAdapter extends RecyclerView.Adapter<ActionHolder> {

        @Override
        public ActionHolder onCreateViewHolder(ViewGroup parent, int viewType) {
            View view = LayoutInflater.from(parent.getContext()).inflate(R.layout.action_item, parent, false);
            return new ActionHolder(view);
        }

        @Override
        public void onBindViewHolder(ActionHolder holder, final int position) {
            final T action = menuItems.get(position);
            holder.actionText.setText(getMenuLabel(action));
            holder.actionText.setTextColor(ColorProvider.PRIMARY_TEXT.getColor());
            holder.actionTag.setImageResource(action.getIconId());
            holder.itemView.setOnClickListener(v -> {
                onActionClicked(action);
                // Sometimes this happens after onSaveInstanceState is called, which throws an Exception if we don't allow state loss
                dismissAllowingStateLoss();
            });
        }

        @Override
        public int getItemCount() {
            return menuItems == null ? 0 : menuItems.size();
        }

    }


}
