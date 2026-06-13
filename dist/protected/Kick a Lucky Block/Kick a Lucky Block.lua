-- ===== Key System (must pass before the script runs) =====
local function __y2k_keygate()
-- ============================================================================
--  Y2k key provider  (drop-in replacement for the Junkie SDK)
--  Talks to YOUR Cloudflare Worker + KV key server (server-side hashing, HWID
--  auto-bind, expiry). CONFIGURE the two URLs below. Server: server-example/.
-- ============================================================================
local Junkie = {}
do
	local KEY_API  = "https://y2k-keys.y2kscript.workers.dev"  -- your deployed Worker (LIVE)
	local KEY_LINK = "https://work.ink/2Dgt/ks-int12887-kq76mlra7lo" -- work.ink key link

	local HttpService = game:GetService("HttpService")
	local function enc(s) local ok, r = pcall(function() return HttpService:UrlEncode(s) end) return ok and r or s end
	local function httpGet(u)
		for _, f in ipairs({
			function() return game:HttpGetAsync(u) end,
			function() return game:HttpGet(u) end,
			function() return request and request({ Url = u, Method = "GET" }).Body end,
		}) do
			local ok, b = pcall(f); if ok and type(b) == "string" then return b end
		end
		return nil
	end
	local function hwid()
		local id
		pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
		if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
		return tostring(id or "unknown")
	end

	function Junkie.get_key_link() return KEY_LINK end
	function Junkie.check_key(key)
		if not key or key == "" then return { valid = false, message = "No key entered" } end
		local hw = hwid()
		local url = KEY_API .. "/check?key=" .. enc(key) .. "&hwid=" .. enc(hw) .. "&t=" .. tostring(os.time())
		local body = httpGet(url)
		if not body then return { valid = false, message = "Key server unreachable" } end
		local b = string.lower(body)
		if string.find(b, "ok", 1, true) then
			getgenv().HWID = hw
			return { valid = true, message = "KEY_VALID", hwid = hw }
		elseif string.find(b, "expired", 1, true) then
			return { valid = false, message = "Key expired" }
		elseif string.find(b, "hwid", 1, true) then
			return { valid = false, message = "Key locked to another device" }
		else
			return { valid = false, message = "Invalid key" }
		end
	end
end


local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local Lighting = game:GetService("Lighting")
local HttpService = game:GetService("HttpService")

local Icons = {
	Shield = "rbxassetid://105619007041452",
	Loading = "rbxassetid://116535712789945",
	Lock = "rbxassetid://114355063515473",
	Key = "rbxassetid://93569468678423",
	Check = "rbxassetid://119783053916823",
	CheckCircle = "rbxassetid://10709790644",
	XCircle = "rbxassetid://10747384394",
	Warning = "rbxassetid://130226573962640",
	Globe = "rbxassetid://10734950309",
	Info = "rbxassetid://94529541997278",
	ExternalLink = "rbxassetid://71038734318580",
	Copy = "rbxassetid://107485544510830",
	Spinner = "rbxassetid://10709767827",
	Database = "rbxassetid://114209748010261",
	Sparkles = "rbxassetid://10709767827",
	ErrorFolder = "rbxassetid://113312905787220",
	Candy = "rbxassetid://10709767827",
	JunkieNewIcon = "rbxassetid://75038032192167"
}

local function hasFileSystemSupport()
    local hasWritefile = pcall(function() return type(writefile) == "function" end)
    local hasReadfile = pcall(function() return type(readfile) == "function" end)
    local hasIsfile = pcall(function() return type(isfile) == "function" end)
    return hasWritefile and hasReadfile and hasIsfile
end

local fileSystemSupported = hasFileSystemSupport()

local function saveVerifiedKey(key)
    if not fileSystemSupported then return false end
    local ok = pcall(function()
        writefile("verified_key.txt", key)
    end)
    return ok
end

local function loadVerifiedKey()
    if not fileSystemSupported then 
        return nil 
    end
    
    local ok, content = pcall(function()
        return readfile("verified_key.txt")
    end)
    
    if not ok or not content then 
        return nil 
    end
    return content
end

local function clearSavedKey()
    if not fileSystemSupported then return false end
    local ok = pcall(function() delfile("verified_key.txt") end)
    return ok
end

local Configuration = {
	ScreenGuiName = "JunkieKeySystem",
	Window = {Size = UDim2.new(0, 333, 0, 500)},
	Colors = {
		Bg = Color3.fromRGB(12, 12, 12),
		Primary = Color3.fromRGB(59, 130, 246),
		PrimaryDark = Color3.fromRGB(37, 99, 235),
		StatusIdle = Color3.fromRGB(249, 115, 22),
		StatusSuccess = Color3.fromRGB(16, 185, 129),
		StatusError = Color3.fromRGB(239, 68, 68),
		StatusVerifying = Color3.fromRGB(59, 130, 246),
		StatusWarning = Color3.fromRGB(254, 188, 46),
		TextMain = Color3.fromRGB(255, 255, 255),
		TextSec = Color3.fromRGB(161, 161, 170),
		TextMuted = Color3.fromRGB(113, 113, 122),
		Border = Color3.fromRGB(255, 255, 255),
		TrafficRed = Color3.fromRGB(255, 95, 87),
		TrafficYellow = Color3.fromRGB(254, 188, 46),
		TrafficGreen = Color3.fromRGB(40, 200, 64),
		Success = Color3.fromRGB(50, 205, 110),
		Error = Color3.fromRGB(245, 70, 90),
		Warning = Color3.fromRGB(255, 200, 50)
	},
	BorderTransparency = 0.15,
	Animations = {
		VeryFast = 0.1,
		Fast = 0.2,
		Medium = 0.4,
		Slow = 0.5,
		VerySlow = 0.6,
		Bounce = 0.6
	},
	Fonts = {
		Title = 24,
		Subtitle = 12,
		Button = 14,
		Input = 16,
		Body = 13,
		Small = 11,
		Tiny = 12
	}
}

local Utils = {}

Utils.Tween = function(obj, props, time, style, dir)
	local t =
		TweenService:Create(
		obj,
		TweenInfo.new(time or 0.3, style or Enum.EasingStyle.Quint, dir or Enum.EasingDirection.Out),
		props
	)
	t:Play()
	return t
end

Utils.CreateCorner = function(parent, radius)
	local corner = Instance.new("UICorner")
	corner.CornerRadius = UDim.new(0, radius or Configuration.CornerRadius)
	corner.Parent = parent
	return corner
end

Utils.Round = function(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius or 12)
	c.Parent = obj
	return c
end

Utils.TweenBack = function(instance, properties, duration)
	return Utils.Tween(instance, properties, duration, Enum.EasingStyle.Back, Enum.EasingDirection.Out)
end

Utils.CreateStroke = function(parent, color, thickness, transparency)
	local stroke = Instance.new("UIStroke")
	stroke.Color = color or Configuration.Colors.Border
	stroke.Thickness = thickness or 1
	stroke.Transparency = transparency or 0.77
	stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	stroke.Parent = parent
	return stroke
end

Utils.Stroke = function(obj, color, thick, trans)
	local s = Instance.new("UIStroke")
	s.Color = color or Color3.new(1, 1, 1)
	s.Thickness = thick or 1
	s.Transparency = trans or 0.9
	s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	s.Parent = obj
	return s
end

Utils.CreateGradient = function(parent, color1, color2, rotation)
	local gradient = Instance.new("UIGradient")
	gradient.Color =
		ColorSequence.new(
		{
			ColorSequenceKeypoint.new(0, color1),
			ColorSequenceKeypoint.new(1, color2)
		}
	)
	gradient.Rotation = rotation or 300
	gradient.Parent = parent
	return gradient
end

local function SetBlur(enabled)
	local blur = Lighting:FindFirstChild("JunkieBlur")
	if enabled then
		if not blur then
			blur = Instance.new("BlurEffect")
			blur.Name = "JunkieBlur"
			blur.Size = 0
			blur.Parent = Lighting
		end
		Utils.Tween(blur, {Size = 24}, Configuration.Animations.Bounce)
	elseif blur then
		Utils.Tween(blur, {Size = 0}, Configuration.Animations.Medium)
		task.delay(
			0.4,
			function()
				blur:Destroy()
			end
		)
	end
end

local ToastSystem = {ActiveToasts = {}, MaxToasts = 3, ToastSpacing = 10}

ToastSystem.Create = function(parent, message, toastType, duration, statusCode)
	local colors = {
		success = Configuration.Colors.Success,
		error = Configuration.Colors.Error,
		warning = Configuration.Colors.Warning,
		info = Configuration.Colors.Primary
	}
	local icons = {
		success = Icons.CheckCircle,
		error = Icons.ErrorFolder,
		warning = Icons.Warning,
		info = Icons.Info
	}
	local toastColor = colors[toastType] or colors.Bg
	local toastIcon = icons[toastType] or nil
	if #ToastSystem.ActiveToasts >= ToastSystem.MaxToasts then
		local oldest = table.remove(ToastSystem.ActiveToasts, 1)
		if oldest and oldest.Parent then
			oldest:Destroy()
		end
	end
	local toastHeight = 56
	local toast = Instance.new("Frame")
	toast.Name = tick()
	toast.Size = UDim2.new(0, 0, 0, toastHeight)
	toast.Position = UDim2.new(0.5, 0, 0, 20)
	toast.AnchorPoint = Vector2.new(0.5, 0)
	toast.BackgroundColor3 = Configuration.Colors.Bg
	toast.BackgroundTransparency = 0.5
	toast.BorderSizePixel = 0
	toast.ZIndex = 300
	toast.ClipsDescendants = true
	toast.Parent = parent
	Utils.Round(toast, 14)
	Utils.CreateStroke(toast, toastColor, 1, 0.1)
	Utils.CreateGradient(toast, Configuration.Colors.Bg, Configuration.Colors.Bg, 1)
	local iconBg = Instance.new("Frame")
	iconBg.Name = "IconBg"
	iconBg.Size = UDim2.new(0, 36, 0, 36)
	iconBg.Position = UDim2.new(0, 12, 0.5, 0)
	iconBg.AnchorPoint = Vector2.new(0, 0.5)
	iconBg.BackgroundColor3 = toastColor
	iconBg.BackgroundTransparency = 0.85
	iconBg.BorderSizePixel = 0
	iconBg.ZIndex = 301
	iconBg.Parent = toast
	Utils.Round(iconBg, 18)
	local icon = Instance.new("ImageLabel")
	icon.Name = "Icon"
	icon.Size = UDim2.new(0, 20, 0, 20)
	icon.Position = UDim2.new(0.5, 0, 0.5, 0)
	icon.AnchorPoint = Vector2.new(0.5, 0.5)
	icon.BackgroundTransparency = 1
	icon.Image = toastIcon
	icon.ImageColor3 = toastColor
	icon.ZIndex = 302
	icon.Parent = iconBg
	local textContainer = Instance.new("Frame")
	textContainer.Name = "TextContainer"
	textContainer.Size = UDim2.new(1, statusCode and -110 or -60, 1, 0)
	textContainer.Position = UDim2.new(0, 56, 0, 0)
	textContainer.BackgroundTransparency = 1
	textContainer.ZIndex = 301
	textContainer.Parent = toast
	local text = Instance.new("TextLabel")
	text.Name = "Message"
	text.Size = UDim2.new(1, 0, 1, 0)
	text.BackgroundTransparency = 1
	text.Text = message or ""
	text.TextColor3 = Configuration.Colors.TextMain
	text.TextSize = Configuration.Fonts.Body
	text.Font = Enum.Font.GothamMedium
	text.TextXAlignment = Enum.TextXAlignment.Left
	text.TextYAlignment = Enum.TextYAlignment.Center
	text.TextWrapped = true
	text.ZIndex = 301
	text.Parent = textContainer
	if statusCode then
		local statusBadge = Instance.new("Frame")
		statusBadge.Name = "StatusBadge"
		statusBadge.Size = UDim2.new(0, 44, 0, 28)
		statusBadge.Position = UDim2.new(1, -12, 0.5, 0)
		statusBadge.AnchorPoint = Vector2.new(1, 0.5)
		statusBadge.BackgroundColor3 = toastColor
		statusBadge.BackgroundTransparency = 0.8
		statusBadge.BorderSizePixel = 0
		statusBadge.ZIndex = 301
		statusBadge.Parent = toast
		Utils.Round(statusBadge, 8)
		Utils.CreateStroke(statusBadge, toastColor, 1, Configuration.BorderTransparency)
		local statusCodeLabel = Instance.new("TextLabel")
		statusCodeLabel.Name = "StatusCode"
		statusCodeLabel.Size = UDim2.new(1, 0, 1, 0)
		statusCodeLabel.BackgroundTransparency = 1
		statusCodeLabel.Text = tostring(statusCode)
		statusCodeLabel.TextColor3 = toastColor
		statusCodeLabel.TextSize = Configuration.Fonts.Small
		statusCodeLabel.Font = Enum.Font.GothamBold
		statusCodeLabel.ZIndex = 302
		statusCodeLabel.Parent = statusBadge
	end
	table.insert(ToastSystem.ActiveToasts, toast)
	ToastSystem.RepositionToasts()
	local targetWidth = 320
	Utils.TweenBack(toast, {Size = UDim2.new(0, targetWidth, 0, toastHeight)}, Configuration.Animations.Medium)
	task.delay(
		duration or 3.5,
		function()
			if toast.Parent then
				Utils.Tween(
					toast,
					{
						Position = UDim2.new(0.5, 0, 0, -80),
						BackgroundTransparency = 1
					},
					Configuration.Animations.Medium
				)
				for i, t in ipairs(ToastSystem.ActiveToasts) do
					if t == toast then
						table.remove(ToastSystem.ActiveToasts, i)
						break
					end
				end
				task.wait(Configuration.Animations.Medium)
				toast:Destroy()
				ToastSystem.RepositionToasts()
			end
		end
	)
	return toast
end

ToastSystem.RepositionToasts = function()
	for i, toast in ipairs(ToastSystem.ActiveToasts) do
		local targetY = 20 + ((i - 1) * (60 + ToastSystem.ToastSpacing))
		Utils.Tween(toast, {Position = UDim2.new(0.5, 0, 0, targetY)}, Configuration.Animations.Medium)
	end
end

local function Build()
	local parent = game:GetService("CoreGui")
	local old = parent:FindFirstChild(Configuration.ScreenGuiName)
	if old then
		old:Destroy()
	end
	local screen = Instance.new("ScreenGui")
	screen.Name = Configuration.ScreenGuiName
	screen.ResetOnSpawn = false
	screen.Parent = parent

	-- Discord banner (top of screen, transparent, blinking + glow)
	local discordBanner = Instance.new("TextLabel")
	discordBanner.Name = "DiscordBanner"
	discordBanner.Size = UDim2.new(0, 400, 0, 32)
	discordBanner.Position = UDim2.new(0.5, 0, 0, 10)
	discordBanner.AnchorPoint = Vector2.new(0.5, 0)
	discordBanner.BackgroundTransparency = 1
	discordBanner.Text = "Join https://discord.gg/EFFKrfFkPQ"
	discordBanner.TextColor3 = Color3.fromRGB(88, 101, 242)
	discordBanner.TextSize = 16
	discordBanner.Font = Enum.Font.GothamBold
	discordBanner.TextTransparency = 0
	discordBanner.Parent = screen

	local bannerStroke = Instance.new("UIStroke")
	bannerStroke.Color = Color3.fromRGB(88, 101, 242)
	bannerStroke.Thickness = 2
	bannerStroke.Transparency = 0.3
	bannerStroke.Parent = discordBanner

	task.spawn(function()
		while discordBanner and discordBanner.Parent do
			Utils.Tween(discordBanner, {TextTransparency = 0.4}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.7}, 0.6)
			task.wait(0.6)
			Utils.Tween(discordBanner, {TextTransparency = 0}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.3}, 0.6)
			task.wait(0.6)
		end
	end)

	local overlay = Instance.new("Frame")
	overlay.Size = UDim2.fromScale(1, 1)
	overlay.BackgroundColor3 = Color3.new(0, 0, 0)
	overlay.BackgroundTransparency = 1
	overlay.Parent = screen
	Utils.Tween(overlay, {BackgroundTransparency = 1}, 1)
	SetBlur(true)
	local main = Instance.new("Frame")
	main.Size = Configuration.Window.Size
	main.Position = UDim2.new(0.5, 0, 0.5, 60)
	main.AnchorPoint = Vector2.new(0.5, 0.5)
	main.BackgroundColor3 = Configuration.Colors.Bg
	main.BackgroundTransparency = 0.2
	main.ClipsDescendants = true
	main.Parent = screen
	Utils.Round(main, 24)
	Utils.Stroke(main, Color3.new(1, 1, 1), 1, 0.92)
	local glass = Instance.new("Frame")
	glass.Size = UDim2.fromScale(1, 1)
	glass.BackgroundColor3 = Color3.new(1, 1, 1)
	glass.BackgroundTransparency = 0.985
	glass.ZIndex = 0
	glass.Parent = main
	Utils.Round(glass, 24)
	local bar = Instance.new("Frame")
	bar.Size = UDim2.new(1, 0, 0, 54)
	bar.BackgroundTransparency = 1
	bar.Parent = main
	local dots = Instance.new("Frame")
	dots.Size = UDim2.new(0, 54, 0, 12)
	dots.Position = UDim2.new(0, 20, 0.5, 0)
	dots.AnchorPoint = Vector2.new(0, 0.5)
	dots.BackgroundTransparency = 1
	dots.Parent = bar
	local dColors = {
		Configuration.Colors.TrafficRed,
		Configuration.Colors.TrafficYellow,
		Configuration.Colors.TrafficGreen
	}
	for i, c in ipairs(dColors) do
		local d = Instance.new("Frame")
		d.Size = UDim2.fromOffset(12, 12)
		d.Position = UDim2.fromOffset((i - 1) * 18, 0)
		d.BackgroundColor3 = c
		d.BorderSizePixel = 0
		d.Parent = dots
		Utils.Round(d, 6)
	end
	local titleText = Instance.new("TextLabel")
	titleText.Size = UDim2.new(1, 0, 1, 0)
	titleText.Text = "JUNKIE"
	titleText.TextColor3 = Color3.new(1, 1, 1)
	titleText.TextTransparency = 0.7
	titleText.TextSize = 10
	titleText.Font = Enum.Font.GothamBold
	titleText.BackgroundTransparency = 1
	titleText.Parent = bar
	local content = Instance.new("ScrollingFrame")
	content.Size = UDim2.new(1, 0, 1, -54)
	content.Position = UDim2.new(0, 0, 0, 54)
	content.BackgroundTransparency = 1
	content.ScrollBarThickness = 0
	content.CanvasSize = UDim2.new(0, 0, 0, 440)
	content.Parent = main
	local list = Instance.new("UIListLayout")
	list.Padding = UDim.new(0, 24)
	list.HorizontalAlignment = Enum.HorizontalAlignment.Center
	list.Parent = content
	local pad = Instance.new("UIPadding")
	pad.PaddingTop = UDim.new(0, 5)
	pad.Parent = content
	local logoContainer = Instance.new("Frame")
	logoContainer.Size = UDim2.fromOffset(80, 80)
	logoContainer.BackgroundColor3 = Configuration.Colors.Primary
	logoContainer.Parent = content
	Utils.Round(logoContainer, 20)
	local grad = Instance.new("UIGradient")
	grad.Color = ColorSequence.new(Configuration.Colors.Primary, Configuration.Colors.PrimaryDark)
	grad.Rotation = 45
	grad.Parent = logoContainer
	local sIcon = Instance.new("ImageLabel")
	sIcon.Size = UDim2.fromScale(1, 1)
	sIcon.Position = UDim2.fromScale(0.5, 0.5)
	sIcon.AnchorPoint = Vector2.new(0.5, 0.5)
	sIcon.Image = Icons.JunkieNewIcon
	sIcon.ScaleType = Enum.ScaleType.Fit
	sIcon.BackgroundTransparency = 1
	sIcon.Parent = logoContainer
	local titleArea = Instance.new("Frame")
	titleArea.Size = UDim2.new(1, 0, 0, 44)
	titleArea.BackgroundTransparency = 1
	titleArea.Parent = content
	local mainTitle = Instance.new("TextLabel")
	mainTitle.Size = UDim2.new(1, 0, 0, 26)
	mainTitle.Text = "Junkie"
	mainTitle.TextColor3 = Color3.new(1, 1, 1)
	mainTitle.TextSize = 26
	mainTitle.Font = Enum.Font.GothamBold
	mainTitle.BackgroundTransparency = 1
	mainTitle.Parent = titleArea
	local subTitle = Instance.new("TextLabel")
	subTitle.Size = UDim2.new(1, 0, 0, 16)
	subTitle.Position = UDim2.fromOffset(0, 28)
	subTitle.Text = "junkie-development.de"
	subTitle.TextColor3 = Configuration.Colors.TextSec
	subTitle.TextSize = 13
	subTitle.Font = Enum.Font.Gotham
	subTitle.BackgroundTransparency = 1
	subTitle.Parent = titleArea
	local statusCard = Instance.new("Frame")
	statusCard.Size = UDim2.new(0, 280, 0, 68)
	statusCard.BackgroundColor3 = Color3.new(1, 1, 1)
	statusCard.BackgroundTransparency = 0.96
	statusCard.Parent = content
	Utils.Round(statusCard, 16)
	local sStroke = Utils.Stroke(statusCard, Color3.new(1, 1, 1), 1, 0.95)
	local sIconBg = Instance.new("Frame")
	sIconBg.Size = UDim2.fromOffset(42, 42)
	sIconBg.Position = UDim2.new(0, 14, 0.5, 0)
	sIconBg.AnchorPoint = Vector2.new(0, 0.5)
	sIconBg.BackgroundColor3 = Configuration.Colors.StatusIdle
	sIconBg.BackgroundTransparency = 0.9
	sIconBg.Parent = statusCard
	Utils.Round(sIconBg, 21)
	local sImg = Instance.new("ImageLabel")
	sImg.Size = UDim2.fromScale(0.5, 0.5)
	sImg.Position = UDim2.fromScale(0.5, 0.5)
	sImg.AnchorPoint = Vector2.new(0.5, 0.5)
	sImg.Image = Icons.Lock
	sImg.ImageColor3 = Configuration.Colors.StatusIdle
	sImg.BackgroundTransparency = 1
	sImg.Parent = sIconBg
	local sLabel = Instance.new("TextLabel")
	sLabel.Size = UDim2.new(1, -70, 0, 14)
	sLabel.Position = UDim2.fromOffset(70, 16)
	sLabel.Text = "CURRENT STATUS"
	sLabel.TextColor3 = Configuration.Colors.TextMuted
	sLabel.TextSize = 10
	sLabel.Font = Enum.Font.GothamBold
	sLabel.TextXAlignment = Enum.TextXAlignment.Left
	sLabel.BackgroundTransparency = 1
	sLabel.Parent = statusCard
	local sValue = Instance.new("TextLabel")
	sValue.Size = UDim2.new(1, -70, 0, 20)
	sValue.Position = UDim2.fromOffset(70, 32)
	sValue.Text = "No key detected"
	sValue.TextColor3 = Configuration.Colors.StatusIdle
	sValue.TextSize = 15
	sValue.Font = Enum.Font.GothamMedium
	sValue.TextXAlignment = Enum.TextXAlignment.Left
	sValue.BackgroundTransparency = 1
	sValue.Parent = statusCard
	local inputFrame = Instance.new("Frame")
	inputFrame.Size = UDim2.new(0, 280, 0, 52)
	inputFrame.BackgroundColor3 = Color3.new(1, 1, 1)
	inputFrame.BackgroundTransparency = 0.975
	inputFrame.Parent = content
	Utils.Round(inputFrame, 14)
	local iStroke = Utils.Stroke(inputFrame, Color3.new(1, 1, 1), 1, 0.95)
	local kIcon = Instance.new("ImageLabel")
	kIcon.Size = UDim2.fromOffset(18, 18)
	kIcon.Position = UDim2.new(0, 14, 0.5, 0)
	kIcon.AnchorPoint = Vector2.new(0, 0.5)
	kIcon.Image = Icons.Key
	kIcon.ImageColor3 = Configuration.Colors.TextMuted
	kIcon.BackgroundTransparency = 1
	kIcon.Parent = inputFrame
	local box = Instance.new("TextBox")
	box.Size = UDim2.new(1, -85, 1, 0)
	box.Position = UDim2.fromOffset(45, 0)
	box.Text = ""
	box.PlaceholderText = "Enter your key..."
	box.TextColor3 = Color3.new(1, 1, 1)
	box.TextSize = 14
	box.Font = Enum.Font.Gotham
	box.BackgroundTransparency = 1
	box.TextXAlignment = Enum.TextXAlignment.Left
	box.Parent = inputFrame
	local paste = Instance.new("ImageButton")
	paste.Size = UDim2.fromOffset(18, 18)
	paste.Position = UDim2.new(1, -14, 0.5, 0)
	paste.AnchorPoint = Vector2.new(1, 0.5)
	paste.Image = Icons.Copy
	paste.ImageColor3 = Configuration.Colors.TextMuted
	paste.BackgroundTransparency = 1
	paste.Parent = inputFrame
	local btnRow = Instance.new("Frame")
	btnRow.Size = UDim2.new(0, 280, 0, 50)
	btnRow.BackgroundTransparency = 1
	btnRow.Parent = content
	local redeem = Instance.new("TextButton")
	redeem.Size = UDim2.new(0.5, -8, 1, 0)
	redeem.BackgroundColor3 = Configuration.Colors.Primary
	redeem.Text = "Redeem"
	redeem.TextColor3 = Color3.new(1, 1, 1)
	redeem.Font = Enum.Font.GothamBold
	redeem.TextSize = 14
	redeem.AutoButtonColor = false
	redeem.Parent = btnRow
	Utils.Round(redeem, 14)
	local getKey = Instance.new("TextButton")
	getKey.Size = UDim2.new(0.5, -8, 1, 0)
	getKey.Position = UDim2.new(0.5, 8, 0, 0)
	getKey.BackgroundColor3 = Color3.new(1, 1, 1)
	getKey.BackgroundTransparency = 0.955
	getKey.Text = "Get Key"
	getKey.TextColor3 = Color3.new(1, 1, 1)
	getKey.Font = Enum.Font.GothamBold
	getKey.TextSize = 14
	getKey.AutoButtonColor = false
	getKey.Parent = btnRow
	Utils.Round(getKey, 14)
	Utils.Stroke(getKey, Color3.new(1, 1, 1), 1, 0.94)
	local function ApplyHover(btn)
		local baseColor = btn.BackgroundColor3
		btn.MouseEnter:Connect(
			function()
				Utils.Tween(
					btn,
					{
						BackgroundColor3 = baseColor:Lerp(Color3.new(1, 1, 1), 0.1)
					},
					0.2
				)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset + 4, btn.Size.Y.Scale, btn.Size.Y.Offset + 2)
					},
					0.2
				)
			end
		)
		btn.MouseLeave:Connect(
			function()
				Utils.Tween(btn, {BackgroundColor3 = baseColor}, 0.2)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset - 4, btn.Size.Y.Scale, btn.Size.Y.Offset - 2)
					},
					0.2
				)
			end
		)
	end
	ApplyHover(redeem)
	ApplyHover(getKey)
	box.Focused:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.5, Thickness = 1.2}, 0.3)
		end
	)
	box.FocusLost:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.95, Thickness = 1}, 0.3)
		end
	)
	local spinConnection
	local dotsThread
	local function SetStatus(state)
		if spinConnection then
			spinConnection:Disconnect()
			spinConnection = nil
			sImg.Rotation = 0
		end
		if dotsThread then
			task.cancel(dotsThread)
			dotsThread = nil
		end
		local color = Configuration.Colors.StatusIdle
		local icon = Icons.Lock
		local text = "No key detected"
		if state == "verifying" then
			color = Configuration.Colors.StatusVerifying
			icon = Icons.Loading
			text = "Verifying access"
			spinConnection =
				RunService.Heartbeat:Connect(
				function(dt)
					if not sImg or not sImg.Parent then
						if spinConnection then
							spinConnection:Disconnect()
						end
						spinConnection = nil
						return
					end
					sImg.Rotation = (sImg.Rotation + dt * 360) % 360
				end
			)
			local dots = {".", "..", "...", ""}
			local i = 1
			dotsThread =
				task.spawn(
				function()
					while sValue and sValue.Parent do
						if not sValue.Text:find("Verifying access", 1, true) then
							break
						end
						sValue.Text = text .. dots[i]
						i = (i % #dots) + 1
						task.wait(0.45)
					end
				end
			)
		elseif state == "success" then
			color = Configuration.Colors.StatusSuccess
			icon = Icons.CheckCircle
			text = "Access Granted"
		elseif state == "error" then
			color = Configuration.Colors.StatusError
			icon = Icons.XCircle
			text = "Invalid Key"
		end
		Utils.Tween(sValue, {TextColor3 = color}, 0.35)
		Utils.Tween(sImg, {ImageColor3 = color}, 0.35)
		Utils.Tween(sIconBg, {BackgroundColor3 = color}, 0.35)
		sValue.Text = text
		sImg.Image = icon
	end
	redeem.MouseButton1Click:Connect(
		function()
			local key = box.Text:upper()
			SetStatus("verifying")
			redeem.Text = "..."
			redeem.Active = false
            local result = Junkie.check_key(key)
			redeem.Active = true
			redeem.Text = "Redeem"
			if not result then
				SetStatus("error")
				ToastSystem.Create(screen, "API request failed: " .. tostring(result), "error")
				return
			end
			if result.valid then
                saveVerifiedKey(key)
                getgenv().SCRIPT_KEY = key
                SetStatus("success")
                ToastSystem.Create(screen, "Access granted!", "success", nil, status)
                task.wait(0.8)
                SetBlur(false)
                Utils.Tween(
                    main,
                    {
                        Position = UDim2.new(0.5, 0, 0.5, 100),
                        BackgroundTransparency = 1
                    },
                    0.7,
                    Enum.EasingStyle.Exponential,
                    Enum.EasingDirection.In
                )
                task.delay(
                    0.7,
                    function()
                        screen:Destroy()
                    end
                )
			else
				SetStatus("error")
				ToastSystem.Create(screen, result.message or "Invalid key", "error", nil, status)
			end
		end
	)
	getKey.MouseButton1Click:Connect(
		function()
			setclipboard(Junkie.get_key_link())
			ToastSystem.Create(screen, "Key link has been copied to clipboard", "success")
		end
	)
	paste.MouseButton1Click:Connect(
		function()
			ToastSystem.Create(screen, "Paste functionality not supported in Roblox (security reasons)", "warning")
		end
	)
	main.Position = UDim2.new(0.5, 0, 0.5, 100)
	main.BackgroundTransparency = 1
	Utils.Tween(
		main,
		{
			Position = UDim2.new(0.5, 0, 0.5, 0),
			BackgroundTransparency = 0.2
		},
		1,
		Enum.EasingStyle.Exponential
	)
	local dragging, dragStart, startPos
	bar.InputBegan:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = true
				dragStart = input.Position
				startPos = main.Position
			end
		end
	)
	UserInputService.InputChanged:Connect(
		function(input)
			if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
				local delta = input.Position - dragStart
				main.Position =
					UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
			end
		end
	)
	UserInputService.InputEnded:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = false
			end
		end
	)
	return screen
end

local savedKey = loadVerifiedKey()
local keyToCheck = savedKey
if not keyToCheck then
    keyToCheck = getgenv().SCRIPT_KEY
end

local result = Junkie.check_key(keyToCheck)
if result and result.valid then
    if result.message == "KEYLESS" then
        getgenv().SCRIPT_KEY = "KEYLESS"
    elseif result.message == "KEY_VALID" then
        if not savedKey and keyToCheck then
            saveVerifiedKey(keyToCheck)
        end
        getgenv().SCRIPT_KEY = keyToCheck
    else
        Build()
    end
else
    Build()
end

while not getgenv().SCRIPT_KEY do
    task.wait(0.1)
end
end
__y2k_keygate()
-- ===== Protected payload =====
-- Protected with Vm runtime. Tampering halts execution.
-- Vm protection runtime (bundled). Do not edit by hand.
local Crypt = (function()
--!nonstrict
-- ============================================================================
--  Crypt.lua  --  lightweight obfuscation / integrity primitives
--  Part of the Vm protection runtime. No external deps. Luau-safe.
--
--  Provides: XOR string cipher, FNV-1a hash, base64, and a small PRNG so the
--  runtime can hide embedded strings (URLs, function names) and verify
--  integrity without leaving plaintext secrets in the bytecode.
-- ============================================================================

local Crypt = {}

local schar, sbyte, ssub, srep = string.char, string.byte, string.sub, string.rep
local tconcat = table.concat
local bxor = bit32 and bit32.bxor or function(a, b)
	local r, p = 0, 1
	while a > 0 or b > 0 do
		local x, y = a % 2, b % 2
		if x ~= y then r = r + p end
		a, b, p = (a - x) / 2, (b - y) / 2, p * 2
	end
	return r
end

-- 32-bit multiply mod 2^32 that stays within double precision (2^53).
-- Splitting the accumulator into hi/lo 16-bit halves keeps every intermediate
-- product under 2^42, so no precision is lost (a plain h*16777619 overflows 2^53).
local function mul32(a, b)
	local ah = (a - a % 65536) / 65536   -- floor(a / 2^16), < 2^16
	local al = a % 65536                  -- a mod 2^16, < 2^16
	return ((ah * b % 65536) * 65536 + al * b) % 4294967296
end

-- FNV-1a 32-bit hash of a string (used for integrity fingerprints)
function Crypt.hash(s)
	local h = 2166136261
	for i = 1, #s do
		h = bxor(h, sbyte(s, i))
		h = mul32(h, 16777619)
	end
	return h
end

-- repeating-key XOR cipher (symmetric). key is a string.
function Crypt.xor(data, key)
	local out, kl = {}, #key
	for i = 1, #data do
		out[i] = schar(bxor(sbyte(data, i), sbyte(key, (i - 1) % kl + 1)))
	end
	return tconcat(out)
end

-- deterministic PRNG (xorshift) seeded from a string; for shuffling/jitter
function Crypt.rng(seed)
	local state = (type(seed) == "string") and Crypt.hash(seed) or (seed or 0x1234567)
	if state == 0 then state = 0x9E3779B9 end
	return function()
		state = bxor(state, (state * 32) % 4294967296)
		state = bxor(state, math.floor(state / 8))
		state = bxor(state, (state * 16384) % 4294967296)
		state = state % 4294967296
		return state / 4294967296
	end
end

-- base64 (so ciphertext survives as a string literal in the bundle)
local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
function Crypt.b64encode(data)
	local out = {}
	for i = 1, #data, 3 do
		local a, b, c = sbyte(data, i), sbyte(data, i + 1), sbyte(data, i + 2)
		local n = a * 65536 + (b or 0) * 256 + (c or 0)
		local c1 = math.floor(n / 262144) % 64
		local c2 = math.floor(n / 4096) % 64
		local c3 = math.floor(n / 64) % 64
		local c4 = n % 64
		out[#out + 1] = ssub(B64, c1 + 1, c1 + 1)
		out[#out + 1] = ssub(B64, c2 + 1, c2 + 1)
		out[#out + 1] = b and ssub(B64, c3 + 1, c3 + 1) or "="
		out[#out + 1] = c and ssub(B64, c4 + 1, c4 + 1) or "="
	end
	return tconcat(out)
end

local B64I
function Crypt.b64decode(data)
	if not B64I then
		B64I = {}
		for i = 1, #B64 do B64I[ssub(B64, i, i)] = i - 1 end
	end
	data = string.gsub(data, "[^" .. B64 .. "]", "")
	local out = {}
	for i = 1, #data, 4 do
		local a = B64I[ssub(data, i, i)] or 0
		local b = B64I[ssub(data, i + 1, i + 1)] or 0
		local c = B64I[ssub(data, i + 2, i + 2)]
		local d = B64I[ssub(data, i + 3, i + 3)]
		local n = a * 262144 + b * 4096 + (c or 0) * 64 + (d or 0)
		out[#out + 1] = schar(math.floor(n / 65536) % 256)
		if c then out[#out + 1] = schar(math.floor(n / 256) % 256) end
		if d then out[#out + 1] = schar(n % 256) end
	end
	return tconcat(out)
end

-- convenience: encrypt a plaintext to a portable token (b64(xor(data,key)))
function Crypt.seal(plaintext, key)
	return Crypt.b64encode(Crypt.xor(plaintext, key))
end
function Crypt.open(token, key)
	return Crypt.xor(Crypt.b64decode(token), key)
end

return Crypt

end)()
local Secure = (function()
--!nonstrict
-- ============================================================================
--  Secure.lua  --  capture real executor functions & expose protected proxies
--
--  THE CORE PROTECTION. At load time (before any spy can install hooks) we grab
--  references to the real executor functions into PRIVATE upvalues, then hand
--  the wrapped script only thin proxies. Because the proxies call the captured
--  originals directly, a spy that later hooks the GLOBAL `request` / `http` /
--  `readfile` never sees the script's calls -- they bypass the global.
--
--  Proxies are wrapped with newcclosure so they read as native C-closures:
--  iscclosure() passes, and getupvalues() is blocked on them by most executors,
--  hiding the captured originals from getgc/upvalue inspection.
-- ============================================================================

local Secure = {}

-- resolve the real global table as early as possible
local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local rawget, rawset = rawget, rawset
local iscc = iscclosure
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction or function(f) return f end

-- list of sensitive globals we proxy. (function-valued globals only)
local CAPTURE = {
	"request", "http_request", "readfile", "writefile", "appendfile", "isfile",
	"isfolder", "listfiles", "makefolder", "delfile", "delfolder", "loadstring",
	"getgenv", "getrawmetatable", "setrawmetatable", "hookfunction", "hookmetamethod",
	"newcclosure", "getnamecallmethod", "setclipboard", "queue_on_teleport",
	"getcustomasset", "fireclickdetector", "firetouchinterest", "fireproximityprompt",
	"isexecutorclosure", "checkcaller", "getconnections", "getcallingscript",
}

-- Capture the real functions. Returns a PRIVATE table (kept as an upvalue by the
-- caller -- never store this in a global).
function Secure.capture()
	local raw = {}

	-- http via the common executor spellings, in priority order
	raw.http = (syn and syn.request) or (http and http.request) or http_request or request
	-- guard: if http appears already hooked (became an l-closure), remember it
	raw.http_tampered = (iscc and raw.http and not iscc(raw.http)) or false

	for _, name in ipairs(CAPTURE) do
		local fn = rawget(realG, name)
		if type(fn) == "function" then
			-- clone where supported so even a later identity-swap of the global
			-- can't reach our reference
			local ok, c = pcall(clonef, fn)
			raw[name] = ok and c or fn
			raw[name .. "_genuine"] = (iscc and iscc(fn)) or false
		end
	end

	-- HttpGet/HttpGetAsync live on `game`; capture bound callers
	local okGame = pcall(function() return game and game.HttpGet end)
	if okGame and game then
		raw.HttpGet = function(url, ...) return game:HttpGet(url, ...) end
		raw.HttpGetAsync = function(url, ...) return game:HttpGetAsync(url, ...) end
	end

	return raw
end

-- Build the proxy table the sandbox exposes. `raw` is the private capture.
-- Each proxy is a newcclosure so its upvalues (the real fn) are not inspectable.
function Secure.proxies(raw)
	local P = {}

	local function wrap(realFn)
		if type(realFn) ~= "function" then return nil end
		return newcc(function(...) return realFn(...) end)
	end

	-- generic passthrough proxies
	for _, name in ipairs(CAPTURE) do
		if raw[name] then P[name] = wrap(raw[name]) end
	end

	-- unified HTTP proxy (the prime spy target). Accepts the standard {Url=...}.
	if raw.http then
		local http = raw.http
		P.request = newcc(function(opts) return http(opts) end)
		P.http_request = P.request
		if syn then P.syn = { request = P.request } end
	end
	if raw.HttpGet then
		P.HttpGet = newcc(function(url, ...) return raw.HttpGet(url, ...) end)
		P.HttpGetAsync = newcc(function(url, ...) return raw.HttpGetAsync(url, ...) end)
	end

	return P
end

-- Snapshot identities so Integrity can detect later replacement of our proxies.
function Secure.fingerprint(P)
	local fp = {}
	for k, v in pairs(P) do
		if type(v) == "function" then fp[k] = v end
	end
	return fp
end

return Secure

end)()
local Environment = (function()
--!nonstrict
-- ============================================================================
--  Environment.lua  --  the sealed sandbox the wrapped script runs inside
--
--  Builds a custom _ENV whose:
--    * function-valued executor globals resolve to PROTECTED PROXIES
--    * everything else falls through to the real globals (so game, workspace,
--      Instance, math, string, task, etc. all work -- full Luau semantics)
--    * writes stay local to the sandbox (script can't pollute real _G)
--    * the metatable is private (Integrity verifies it wasn't swapped)
--
--  This is the isolation layer: the script believes it has a normal global
--  environment, but its sensitive calls are routed through the Vm.
-- ============================================================================

local Environment = {}

function Environment.build(proxies, realG)
	realG = realG or (getgenv and getgenv()) or _G

	-- the sandbox's own storage for globals the script defines
	local store = {}

	-- private metatable (kept out of the sandbox; Integrity holds a ref)
	local mt = {}

	mt.__index = function(_, key)
		-- 1. protected proxy?
		local p = proxies[key]
		if p ~= nil then return p end
		-- 2. script-local global?
		local s = store[key]
		if s ~= nil then return s end
		-- 3. fall through to the real environment
		return realG[key]
	end

	mt.__newindex = function(_, key, value)
		-- keep all writes inside the sandbox (never touch real globals)
		store[key] = value
	end

	-- unique private lock token. __metatable makes getmetatable(env) return THIS
	-- (hiding the real mt) and makes setmetatable(env, ...) error -- so the env's
	-- metatable cannot be swapped. Integrity verifies this token is still in place.
	local lock = {}
	mt.__metatable = lock

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store, lock
end

return Environment

end)()
local Integrity = (function()
--!nonstrict
-- ============================================================================
--  Integrity.lua  --  anti-tamper / anti-penetration
--
--  Verifies the runtime hasn't been hooked or swapped, both at startup and via
--  a background watchdog. On tamper it triggers a caller-supplied onTamper
--  (the Vm wipes the sandbox + halts).
--
--  Checks:
--   * capture genuineness   -- were the executor funcs already hooked at capture?
--   * proxy identity         -- have our proxies been replaced since fingerprint?
--   * env seal               -- is the sandbox __index/__newindex intact?
--   * hostile introspection  -- is something actively decompiling/hooking us?
--   * source checksum        -- does the protected payload still match?
-- ============================================================================

local Integrity = {}

local iscc = iscclosure
local getus = getupvalues or (debug and debug.getupvalues)

-- 1. Were any captured executor functions already hooks (l-closures) at capture?
function Integrity.checkCapture(raw)
	local suspicious = {}
	if raw.http_tampered then suspicious[#suspicious + 1] = "http" end
	for k, v in pairs(raw) do
		if string.sub(k, -8) == "_genuine" and v == false then
			suspicious[#suspicious + 1] = string.sub(k, 1, -9)
		end
	end
	return suspicious
end

-- 2. Our proxies must still be the exact functions we created.
function Integrity.checkProxies(P, fingerprint)
	for k, original in pairs(fingerprint) do
		if P[k] ~= original then return false, k end
	end
	return true
end

-- 3. The sandbox env metatable must be intact (not re-pointed to leak globals).
function Integrity.checkEnv(env, expectedMT)
	local mt = getmetatable(env)
	if mt ~= expectedMT then return false, "metatable" end
	return true
end

-- 4. Best-effort: detect if our own proxies have become inspectable (a sign a
--    de-hook tool unwrapped the cclosure). On a healthy executor getupvalues on
--    a newcclosure should be empty/blocked; non-empty => someone unwrapped it.
function Integrity.checkOpaque(P)
	if not getus then return true end
	for _, v in pairs(P) do
		if type(v) == "function" then
			local ok, ups = pcall(getus, v)
			if ok and type(ups) == "table" and next(ups) ~= nil then
				return false
			end
		end
	end
	return true
end

-- run all startup checks; returns ok, reason
function Integrity.startup(ctx)
	local sus = Integrity.checkCapture(ctx.raw)
	if #sus > 0 and ctx.strict then
		return false, "capture-hooked:" .. table.concat(sus, ",")
	end
	local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
	if not okP then return false, "proxy-swapped:" .. tostring(badKey) end
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envLock)
	if not okE then return false, "env-" .. tostring(why) end
	if not Integrity.checkOpaque(ctx.proxies) then return false, "opaque-broken" end
	return true
end

-- background watchdog: re-run cheap checks on an interval and self-destruct.
-- Spawns through the Memory scope (ctx.mem) so the thread is tracked and
-- cancelled on cleanup -- it can never leak past the script's lifetime.
function Integrity.watchdog(ctx, onTamper)
	local wait_ = (task and task.wait) or wait
	local body = function()
		while ctx.alive do
			wait_(ctx.interval or 2)
			if not ctx.alive then return end
			local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
			local okE = Integrity.checkEnv(ctx.env, ctx.envLock)
			if not okP or not okE then
				ctx.alive = false
				pcall(onTamper, okP and "env" or ("proxy:" .. tostring(badKey)))
				return
			end
		end
	end
	if ctx.mem and ctx.mem.spawn then
		ctx.mem:spawn(body)
	else
		local spawn = (task and task.spawn) or spawn
		if spawn then spawn(body) end
	end
end

return Integrity

end)()
local Stealth = (function()
--!nonstrict
-- ============================================================================
--  Stealth.lua  --  comprehensive environment spoofing / anti-detection
--
--  Covers the full sUNC executor surface (docs.sunc.su). For each function an
--  anti-cheat could use to fingerprint the executor, detect hooks, or scan for
--  injected objects, we install a fake that answers "clean" -- while leaving the
--  function usable for everyone else.
--
--  Technique: hookfunction (rewrites the function OBJECT, so even a reference
--  the AC captured early is affected), replacement wrapped in newcclosure (stays
--  a C-closure -> passes iscclosure). Everything pcall-guarded; only spoofs what
--  the executor actually exposes.
--
--  HONEST: beats ACs that read these globals at runtime and trust them. Does NOT
--  beat an AC that ran fully before you, re-implements checks in its own VM, or
--  validates server-side. Raises the bar across games.
-- ============================================================================

local Stealth = {}

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction
local hookf = hookfunction
local cloneref_ = cloneref or function(x) return x end
local rawget, rawset = rawget, rawset

-- private registries (weak so we never pin objects alive)
local hiddenObjs = setmetatable({}, { __mode = "k" })  -- hide from gc/instance scans
local genuineFns = setmetatable({}, { __mode = "k" })  -- report as un-hooked / ours
local ourScripts = setmetatable({}, { __mode = "k" })  -- hide script bytecode/closure
local installed  = false

function Stealth.hide(o)        if o ~= nil then hiddenObjs[o] = true end return o end
function Stealth.markGenuine(f) if type(f) == "function" then genuineFns[f] = true end return f end
function Stealth.hideScript(s)  if s ~= nil then ourScripts[s] = true end return s end

-- ---- hook helpers ---------------------------------------------------------
-- CRITICAL: after hookfunction(real, repl), the `real` OBJECT behaves like repl.
-- So the replacement must NOT call `real` on its passthrough path (that would be
-- infinite recursion -> C stack overflow). We clone the original FIRST and have
-- the replacement call the unhooked clone. If we can't clone, we fall back to a
-- plain global swap (which leaves `real` itself untouched, so calling it is safe).
local function emplace(container, name, build)
	if type(container) ~= "table" then return end
	local real = rawget(container, name)
	if type(real) ~= "function" then return end
	if hookf and clonef then
		local okc, orig = pcall(clonef, real)
		if okc and type(orig) == "function" then
			local repl = newcc(build(orig))         -- repl -> clone (unhooked): safe
			genuineFns[repl] = true; hiddenObjs[repl] = true
			if pcall(hookf, real, repl) then return end
		end
	end
	-- fallback: global/table swap, repl -> real (real is NOT hooked here): safe
	local repl = newcc(build(real))
	genuineFns[repl] = true; hiddenObjs[repl] = true
	pcall(rawset, container, name, repl)
end

local function spoof(name, build)            emplace(realG, name, build) end
local function spoofIn(tbl, name, build)     emplace(tbl, name, build) end

-- filter our hidden/genuine objects out of an array-like result table.
local function filterArray(t)
	if type(t) ~= "table" then return t end
	local out = {}
	for i = 1, #t do
		local v = t[i]
		if not (hiddenObjs[v] or genuineFns[v]) then out[#out + 1] = v end
	end
	return out
end

-- ===========================================================================
function Stealth.install(opts)
	if installed then return end
	installed = true
	opts = opts or {}
	local fakeName = opts.spoofName            -- nil => "no executor"
	local fakeVer  = opts.spoofVersion or "1.0.0"

	-- DISGUISE: a real game LocalScript (cloneref'd) to report as the "calling
	-- script", so introspection sees a legit script instead of getcallingscript()
	-- == nil (which screams "injected"). On by default; opts.disguise=false to skip.
	local decoyScript = nil
	if opts.disguise ~= false then
		pcall(function()
			local lp = game:GetService("Players").LocalPlayer
			local char = lp and lp.Character
			decoyScript = (char and char:FindFirstChild("Animate"))
				or (lp and lp:FindFirstChildWhichIsA("LocalScript", true))
		end)
		if decoyScript then pcall(function() decoyScript = cloneref_(decoyScript) end) end
	end

	-- 1) IDENTITY ----------------------------------------------------------
	for _, n in ipairs({ "identifyexecutor", "getexecutorname", "iexecutor" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end

	-- 2) CLOSURE CHECKS ----------------------------------------------------
	spoof("iscclosure",       function(r) return function(f) if genuineFns[f] then return true  end return r(f) end end)
	spoof("isexecutorclosure",function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("isourclosure",     function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("islclosure",       function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("checkcaller",      function(r) return function() return false end end)
	-- stable fake hash for our funcs so repeated checks stay consistent
	spoof("getfunctionhash",  function(r) return function(f) if genuineFns[f] then return "00000000000000000000000000000000" end return r(f) end end)

	-- 3) ENVIRONMENT / GC scans -- strip our objects ----------------------
	spoof("getgc",     function(r) return function(...) return filterArray(r(...)) end end)
	spoof("filtergc",  function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	spoof("getreg",    function(r) return function(...) return filterArray(r(...)) end end)
	-- getgenv/getrenv must keep identity (callers rely on it); objects already hidden via getgc

	-- 4) INSTANCE scans -- strip our injected instances -------------------
	spoof("getinstances",    function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getnilinstances", function(r) return function(...) return filterArray(r(...)) end end)

	-- 5) SCRIPT scans -- hide our scripts/closures ------------------------
	spoof("getloadedmodules", function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getrunningscripts",function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getscripts",       function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] or s == nil then return decoyScript end return s end end)
	spoof("getscriptbytecode",function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscriptclosure", function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscripthash",    function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	spoof("getsenv",          function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- 6) DEBUG introspection -- blank out for OUR functions ---------------
	if debug then
		spoofIn(debug, "getupvalue",  function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getupvalues", function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getconstant", function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getconstants",function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getproto",    function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getprotos",   function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
	end
	-- top-level mirrors (some executors expose these globally too)
	for _, n in ipairs({ "getupvalue","getupvalues","getconstant","getconstants","getproto","getprotos" }) do
		spoof(n, function(r) return function(f, ...)
			if genuineFns[f] then
				if string.sub(n, -1) == "s" then return {} end
				return nil
			end
			return r(f, ...)
		end end)
	end

	-- 7) common executor extras (Volt/Synapse/etc. spellings that may exist) ----
	for _, n in ipairs({ "getexecutorname", "getexecutor", "getexecutorinfo" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end
	-- decompiler-style probes: refuse on our scripts
	for _, n in ipairs({ "decompile", "disassemble", "dumpstring" }) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	end

	-- 7b) Potassium / extended closure + thread + hook checks --------------
	-- the big one: isfunctionhooked must say NO for the funcs your cheat hooks
	spoof("isfunctionhooked", function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isnewcclosure",    function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isourclosure",     function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	-- "is this the executor / a hook thread" -> no
	spoof("isourthread",      function(r) return function() return false end end)
	-- thread/script linkage: don't reveal our scripts
	spoof("getscriptfromthread", function(r) return function(t, ...) local s = r(t, ...) if ourScripts[s] then return nil end return s end end)
	spoof("getscriptthread",     function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("gettenv",             function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- Potassium oth.* (original-thread hooking) table
	local oth = rawget(realG, "oth")
	if type(oth) == "table" then
		spoofIn(oth, "is_hook_thread", function(r) return function() return false end end)
	end

	-- debug.* extras present on Potassium
	if debug then
		spoofIn(debug, "getcallstack", function(r) return function(...) return r(...) end end)  -- seam: frames aren't our objects
		-- getregistry: return a filtered COPY with our objects removed (AC scans are read-only)
		spoofIn(debug, "getregistry", function(r) return function(...)
			local reg = r(...)
			if type(reg) ~= "table" then return reg end
			local out = {}
			for k, v in pairs(reg) do
				if not (hiddenObjs[k] or hiddenObjs[v] or genuineFns[k] or genuineFns[v]) then
					out[k] = v
				end
			end
			return out
		end end)
		spoofIn(debug, "getinfo", function(r) return function(...) return r(...) end end)  -- seam
	end

	-- metatable seams: only safe to touch CONDITIONALLY. We do NOT blanket-fake
	-- getrawmetatable/getnamecallmethod -- faking the real game metatable breaks
	-- everything. If YOUR cheat hooks __namecall, register the clean function via
	-- Stealth.markGenuine(yourHook) and add a targeted getrawmetatable spoof.

	-- 8) USER-SUPPLIED EXTENSIONS (add Volt-specific names without editing code) -
	--    opts.identity   = { "voltname", ... }     -> spoofed like identifyexecutor
	--    opts.gcFilters  = { "somelist", ... }     -> array results have our objs removed
	--    opts.genuine    = { "iscustom", ... }     -> return clean for our funcs
	--    opts.scriptHide = { "getbytecode2", ... } -> return nothing for our scripts
	for _, n in ipairs(opts.identity or {}) do
		spoof(n, function() return function() if fakeName then return fakeName, fakeVer end return nil end end)
	end
	for _, n in ipairs(opts.gcFilters or {}) do
		spoof(n, function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	end
	for _, n in ipairs(opts.genuine or {}) do
		spoof(n, function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	end
	for _, n in ipairs(opts.scriptHide or {}) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	end

	return true
end

return Stealth

end)()
local Memory = (function()
--!nonstrict
-- ============================================================================
--  Memory.lua  --  resource scope + leak/overflow protection
--
--  Every thread, connection and disposable the VM creates is registered in a
--  scope. When the script ends (return, error, or tamper) the scope is torn down
--  deterministically: threads cancelled, connections disconnected, tables
--  cleared, GC forced. Plus a budget guard that collects GC the moment memory
--  crosses a threshold, so a runaway/hostile script can't balloon the VM.
--
--  Design notes:
--   * Registries that hold game objects use WEAK keys so they never pin memory.
--   * The scope holds STRONG refs to threads/connections (so it can cancel them)
--     but cleanup is GUARANTEED to run, bounding their lifetime.
--   * Counters are capped; nothing grows unbounded.
-- ============================================================================

local Memory = {}
Memory.__index = Memory

local taskLib   = task
local taskSpawn = (taskLib and taskLib.spawn) or spawn
local taskWait  = (taskLib and taskLib.wait) or wait
local taskDefer = (taskLib and taskLib.defer) or taskSpawn
local taskCancel = taskLib and taskLib.cancel
local cg = collectgarbage

local MAX_TRACKED = 4096   -- hard cap so the bookkeeping itself can't leak

function Memory.new()
	return setmetatable({
		alive = true,
		threads = {},
		conns = {},
		disposers = {},
		count = 0,
	}, Memory)
end

local function bounded(self)
	return self.count < MAX_TRACKED
end

-- spawn a tracked thread (auto-cancelled on cleanup)
function Memory:spawn(fn)
	if not self.alive or not bounded(self) then return end
	local co = taskSpawn(fn)
	self.threads[#self.threads + 1] = co
	self.count = self.count + 1
	return co
end

-- track an arbitrary resource with a disposer
function Memory:track(obj, dispose)
	if not self.alive or not bounded(self) then return obj end
	if dispose then
		self.disposers[#self.disposers + 1] = dispose
		self.count = self.count + 1
	end
	return obj
end

-- track a signal connection (auto-disconnected on cleanup)
function Memory:connect(signal, fn)
	if not self.alive or not bounded(self) then return end
	local ok, c = pcall(function() return signal:Connect(fn) end)
	if ok and c then
		self.conns[#self.conns + 1] = c
		self.count = self.count + 1
		return c
	end
end

-- deterministic teardown -- safe to call multiple times
function Memory:cleanup()
	if not self.alive then return end
	self.alive = false
	for _, c in ipairs(self.conns) do
		pcall(function() if c.Disconnect then c:Disconnect() elseif c.disconnect then c:disconnect() end end)
	end
	if taskCancel then
		for _, co in ipairs(self.threads) do pcall(taskCancel, co) end
	end
	for _, d in ipairs(self.disposers) do pcall(d) end
	self.conns, self.threads, self.disposers, self.count = {}, {}, {}, 0
	if cg then pcall(cg, "collect") end
end

-- memory-budget guard: force GC when usage crosses the threshold; if it stays
-- over after a collect, escalate to onOverflow (the Vm halts).
function Memory:guard(opts)
	opts = opts or {}
	local budgetKB = opts.budgetKB or 700000   -- ~700 MB ceiling by default
	local interval = opts.interval or 4
	self:spawn(function()
		while self.alive do
			taskWait(interval)
			if not self.alive then return end
			local used = cg and cg("count") or 0     -- KB
			if used > budgetKB then
				if cg then pcall(cg, "collect") end
				used = cg and cg("count") or 0
				if used > budgetKB and opts.onOverflow then
					pcall(opts.onOverflow, used)
					return
				end
			end
		end
	end)
end

return Memory

end)()
local Defense = (function()
--!nonstrict
-- ============================================================================
--  Defense.lua  --  detect tools SPYING on your script (anti-tamper)
--
--  These detect OTHER exploiters' inspection tools so your script can react
--  (halt / hide) before its logic or remotes are stolen:
--    * HTTP spy      -- request/http hooked (closure-type check vs captured original)
--    * namecall hook -- __namecall identity changed (IY-style stack inspection)
--    * remote spy    -- gcinfo spike on FireServer (spies deep-clone args)  [opt-in]
--    * Dex explorer  -- weak-table service-cache persistence                [opt-in]
--
--  IMPORTANT: this is ANTI-SPY (protect your code from other exploiters), NOT
--  anti-cheat. It does nothing against the GAME's AC -- and the remote/dex probes
--  even ADD client AC surface (they fire a remote / force GC). Keep those opt-in.
-- ============================================================================

local Defense = {}

local gcinfo_   = gcinfo or function() return (collectgarbage and collectgarbage("count")) or 0 end
local cloneref_ = cloneref or function(x) return x end
local collect   = collectgarbage
local iscc      = iscclosure       -- captured at load; Stealth passes through for non-ours
local dbinfo    = debug and debug.info

-- 1) HTTP spy: a spy hooks the global request -> it becomes an l-closure -------
-- get the real __namecall fn via an errored game:IsA() ----------------------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end

local function remoteSpike()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	return (ok and type(spike) == "number") and spike or 0
end

-- BASELINE: snapshot the environment AFTER your script has set up its own hooks,
-- so YOUR hooks are treated as "normal". Only CHANGES after this (a spy) trigger.
-- Until baseline() is called, the change-detectors stay silent (no false positives).
Defense._snap = nil
function Defense.baseline()
	local realG = (getgenv and getgenv()) or _G
	Defense._snap = {
		ready = true,
		nc = (actualNamecall()),
		request = rawget(realG, "request"),
		http_request = rawget(realG, "http_request"),
		getgc = rawget(realG, "getgc"),     -- a dumper re-hooking getgc -> identity change
		spike = remoteSpike(),
	}
	return true
end

-- getgc-scan: someone re-hooked getgc (a memory scanner/dumper) after baseline
function Defense.detectGetgcHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	local cur = rawget(realG, "getgc")
	if cur and s.getgc and cur ~= s.getgc then return true, "getgc re-hooked (memory scan)" end
	return false
end

-- spy-tool GLOBALS (Hydroxide/SimpleSpy/etc. set flags or tables in getgenv)
local SPY_GLOBALS = { "Hydroxide", "oh_load", "SimpleSpy", "SimpleSpyExecuted", "RemoteSpyV3", "IY_LOADED" }
function Defense.detectSpyGlobals()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		for _, n in ipairs(SPY_GLOBALS) do
			if rawget(g, n) ~= nil then return true, "global " .. n end
		end
	end
	return false
end

-- 1) HTTP spy: the request function IDENTITY changed since baseline (newly hooked)
function Defense.detectHttpSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if cur and s[n] and cur ~= s[n] then return true, n .. " changed after baseline" end
	end
	return false
end

-- 2) namecall hook: __namecall identity changed since baseline
function Defense.detectNamecallHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local nc = actualNamecall()
	if s.nc and nc and nc ~= s.nc then return true, "__namecall changed after baseline" end
	return false
end

-- 3) remote spy: gc spike on FireServer rose ABOVE the baseline (a new arg-cloner)
function Defense.detectRemoteSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local spike = remoteSpike()
	if spike > (s.spike or 0) + 64 then
		return true, "FireServer gc spike " .. tostring(spike)
	end
	return false
end

-- 4a) Infinite Yield (and similar admin tools) set a known global flag --------
function Defense.detectInfiniteYield()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		if rawget(g, "IY_LOADED") == true then return true, "Infinite Yield" end
	end
	return false
end

-- 4b) Spy/explorer GUIs (Dex, RemoteSpy, SimpleSpy, Hydroxide, IY window) ------
-- scans CoreGui, the executor-hidden gui (gethui), and PlayerGui by exact name.
-- PRECISE name matching: exact known names, plus controlled version patterns,
-- so we don't false-positive on legit GUIs (e.g. "Dexterity" must NOT match "dex").
local EXACT = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true, ["remote spy"] = true,
	["simplespy"] = true, ["simple spy"] = true, ["hydroxide"] = true,
}
local function isSpyName(nm)
	if EXACT[nm] then return true end
	if string.match(nm, "^dex%s*v?%d") then return true end          -- "dex v4", "dex 5"
	if string.match(nm, "^remotespy") then return true end
	if string.match(nm, "^simplespy") then return true end
	if string.match(nm, "^hydroxide") then return true end
	return false
end
function Defense.detectSpyGui()
	local parents = {}
	pcall(function() parents[#parents + 1] = game:GetService("CoreGui") end)
	if gethui then pcall(function() parents[#parents + 1] = gethui() end) end
	pcall(function()
		local pg = game:GetService("Players").LocalPlayer:FindFirstChild("PlayerGui")
		if pg then parents[#parents + 1] = pg end
	end)
	for _, p in ipairs(parents) do
		local ok, kids = pcall(function() return p:GetChildren() end)
		if ok then
			for _, c in ipairs(kids) do
				if isSpyName(string.lower(c.Name)) then return true, "GUI: " .. c.Name end
			end
		end
	end
	return false
end

-- 4) Dex: it strong-caches services, so a weak ref survives a forced GC -------
function Defense.detectDex()
	local ok, persisted = pcall(function()
		local weak = setmetatable({}, { __mode = "v" })
		weak[1] = cloneref_(game:GetService("TestService"))
		weak[1] = weak[1]   -- (kept only in the weak table after this scope)
		if collect then for _ = 1, 3 do pcall(collect, "collect") end end
		return weak[1] ~= nil
	end)
	return ok and persisted == true
end

-- SaveInstance guard: hook saveinstance-family so a game/script DUMP is caught
-- the moment it's attempted. Call once (from the watchdog) with the reaction.
function Defense.installSaveGuard(onDetect)
	local realG = (getgenv and getgenv()) or _G
	local newcc_ = newcclosure or function(f) return f end
	local hookf, clonef = hookfunction, clonefunction
	for _, n in ipairs({ "saveinstance", "synsaveinstance", "SaveInstance", "saveplace" }) do
		local f = rawget(realG, n)
		if type(f) == "function" and hookf and clonef then
			local ok, orig = pcall(clonef, f)
			if ok then
				pcall(hookf, f, newcc_(function(...)
					pcall(onDetect, "saveinstance", n)
					return orig(...)
				end))
			end
		end
	end
end

-- run a scan; returns array of { name = , detail = }
function Defense.scan(opts)
	opts = opts or {}
	local found = {}
	local function run(enabled, fn, name, arg)
		if not enabled then return end
		local ok, detail = fn(arg)
		if ok then found[#found + 1] = { name = name, detail = detail or "" } end
	end
	run(opts.iy ~= false,        Defense.detectInfiniteYield, "infinite-yield")
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- Dex/RemoteSpy/IY window
	run(opts.globals ~= false,   Defense.detectSpyGlobals,    "spy-global")  -- Hydroxide/SimpleSpy/etc.
	run(opts.http ~= false,      Defense.detectHttpSpy,       "http-spy")
	run(opts.namecall ~= false,  Defense.detectNamecallHook,  "namecall-hook")
	run(opts.getgc ~= false,     Defense.detectGetgcHook,     "getgc-scan")  -- dumper re-hooked getgc
	run(opts.remote == true,     Defense.detectRemoteSpy,     "remote-spy")  -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,           "dex")         -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	-- proactive SaveInstance dump guard (fires the moment a dump is attempted)
	pcall(Defense.installSaveGuard, onDetect)
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
		-- baseline after a grace period so the script's OWN hooks aren't flagged
		-- (Vm also baselines right after the main chunk; whichever fires first wins).
		local graceUntil = (tick and tick() or 0) + (opts.gracePeriod or 4)
		while ctx.alive do
			n = n + 1
			if not (Defense._snap and Defense._snap.ready) and (tick and tick() or 0) >= graceUntil then
				pcall(Defense.baseline)
			end
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui, globals = opts.globals,
				http = opts.http, namecall = opts.namecall, getgc = opts.getgc,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				local h = hits[1]
				local need = NOISY[h.name] and 2 or 1        -- reliable = instant, noisy = confirm twice
				if h.name == lastHit then confirm = confirm + 1
				else lastHit, confirm = h.name, 1 end
				if confirm >= need then
					pcall(onDetect, h.name, h.detail)
					return
				end
			else
				lastHit, confirm = nil, 0
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Neuter = (function()
--!nonstrict
-- ============================================================================
--  Neuter.lua  --  best-effort anti-cheat neutralizer (with honest reporting)
--
--  Attempts, in order, every CLIENT-SIDE technique to blind an AC, and REPORTS
--  the outcome of each. If it can't bypass, it says so loudly:
--      "AC bypass fail (error; <reason>)"
--  rather than silently pretending you're undetected.
--
--  Strategies:
--    1. global-spoof   -- replace detection globals with clean-answering versions
--    2. upvalue-patch  -- find ACs that captured detection fns as upvalues and
--                         debug.setupvalue them to our clean versions
--    3. table-patch    -- replace detection fns held in (writable) state tables
--                         (reaches some VM-style ACs)
--    4. report-block   -- best-effort: neutralize the global HTTP request path
--
--  HARD TRUTH (always reported): this is CLIENT-SIDE only. An AC that is
--  VM-obfuscated (functions buried in encrypted state -> nothing to patch) or
--  that validates SERVER-SIDE cannot be bypassed from here. Rivals is both.
-- ============================================================================

local Neuter = {}

local newcc   = newcclosure or function(f) return f end
local getgc_  = getgc
local getups  = getupvalues or (debug and debug.getupvalues)
local setup   = debug and debug.setupvalue
local realG   = (getgenv and getgenv()) or _G
local rawget, rawset = rawget, rawset

local SCAN_CAP = 300000

-- clean-answering replacements: AC sees "no executor, nothing hooked"
local function replacements()
	local R = {}
	R.identifyexecutor   = newcc(function() return nil end)
	R.getexecutorname    = newcc(function() return nil end)
	R.getexecutor        = newcc(function() return nil end)
	R.iscclosure         = newcc(function() return true end)   -- everything looks native
	R.isexecutorclosure  = newcc(function() return false end)
	R.isourclosure       = newcc(function() return false end)
	R.islclosure         = newcc(function() return false end)
	R.isfunctionhooked   = newcc(function() return false end)
	R.checkcaller        = newcc(function() return false end)
	R.isourthread        = newcc(function() return false end)
	return R
end

-- map ORIGINAL function identity -> replacement (for patching captured refs)
local function identityMap(R)
	local m = {}
	for name, repl in pairs(R) do
		local orig = rawget(realG, name)
		if type(orig) == "function" then m[orig] = repl end
	end
	return m
end

-- 1) global spoof -----------------------------------------------------------
function Neuter.globalSpoof(R)
	local n = 0
	for name, repl in pairs(R) do
		if type(rawget(realG, name)) == "function" then
			if hookfunction and clonefunction then
				local ok, orig = pcall(clonefunction, rawget(realG, name))
				if ok then pcall(hookfunction, rawget(realG, name), repl) else pcall(rawset, realG, name, repl) end
			else
				pcall(rawset, realG, name, repl)
			end
			n = n + 1
		end
	end
	return n > 0, "spoofed " .. n .. " globals", 0
end

-- 2) upvalue patch ----------------------------------------------------------
function Neuter.patchUpvalues(idmap)
	if not (getgc_ and getups and setup) then return false, "no getgc/debug.setupvalue" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, fn in ipairs(getgc_(false) or getgc_()) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(fn) == "function" then
				local oku, ups = pcall(getups, fn)
				if oku and type(ups) == "table" then
					for i, uv in pairs(ups) do
						if idmap[uv] then
							if pcall(setup, fn, i, idmap[uv]) then patched = patched + 1 end
						end
					end
				end
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " captured upvalue(s) of " .. scanned .. " closures", patched
end

-- 3) table patch (reaches some VM-style ACs that read fns from state tables) -
function Neuter.patchTables(idmap)
	if not getgc_ then return false, "no getgc" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, t in ipairs(getgc_(true)) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(t) == "table" then
				pcall(function()
					for k, v in pairs(t) do
						if idmap[v] then
							if pcall(function() t[k] = idmap[v] end) then patched = patched + 1 end
						end
					end
				end)
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " table slot(s)", patched
end

-- 4) report block (best-effort) --------------------------------------------
function Neuter.blockReporting()
	-- We can only neutralize a report path we can see. The global request is
	-- proxied by Secure already; an AC-internal report channel inside a VM is
	-- not generically locatable, so report this honestly.
	return false, "report channel not generically locatable (AC-internal)"
end

-- orchestrate ---------------------------------------------------------------
function Neuter.run(opts)
	opts = opts or {}
	local logf = opts.log or function(m) pcall(warn, m) end
	local R = replacements()
	local idmap = identityMap(R)

	local results, patched = {}, 0
	local function strat(name, fn, ...)
		local ok, detail, n = fn(...)
		results[#results + 1] = { name = name, ok = ok, detail = detail }
		if type(n) == "number" then patched = patched + n end
		logf("[Neuter] " .. name .. ": " .. (ok and "OK" or "FAIL") .. " -- " .. tostring(detail))
	end

	strat("global-spoof",  Neuter.globalSpoof, R)
	strat("upvalue-patch", Neuter.patchUpvalues, idmap)
	strat("table-patch",   Neuter.patchTables, idmap)
	strat("report-block",  Neuter.blockReporting)

	-- VERDICT (honest)
	local verdict
	if patched > 0 then
		verdict = "client checks neutralized (" .. patched .. " refs patched). "
			.. "WARNING: server-side validation is NOT affected -- this is not full immunity."
		logf("[Neuter] result: PARTIAL -- " .. verdict)
	else
		verdict = "no patchable detection refs found -- AC is VM-obfuscated/absent or "
			.. "captures privately; nothing to neutralize client-side."
		logf("AC bypass fail (error; " .. verdict .. ")")
	end

	return { patched = patched, results = results, ok = patched > 0, verdict = verdict }
end

return Neuter

end)()
local License = (function()
--!nonstrict
-- ============================================================================
--  License.lua  --  key / HWID whitelist, expiry, server validation, delivery
--
--  Anti-leak core. A protected script can require a valid KEY (+ optional HWID
--  lock) before it runs, enforce an EXPIRY, and/or fetch its real payload from
--  YOUR server only after the key checks out (so a leaked file is useless).
--
--  Validation order (any you configure):
--    1. expiry      -- refuse if past opts.expiry (server time when possible)
--    2. local keys  -- opts.keys = { "KEY1", ... } embedded allow-list
--    3. server      -- GET opts.endpoint?key=..&hwid=..  -> body must contain "ok"
--  If none configured, it allows (no license).
-- ============================================================================

local License = {}

local function httpGet(url)
	local fns = {
		function() return game:HttpGetAsync(url) end,
		function() return game:HttpGet(url) end,
		function() return request and request({ Url = url, Method = "GET" }).Body end,
	}
	for _, f in ipairs(fns) do
		local ok, body = pcall(f)
		if ok and type(body) == "string" then return body end
	end
	return nil
end

-- stable per-machine id
function License.hwid()
	local id
	pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
	if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
	return tostring(id or "unknown")
end

-- tamper-resistant time: try a web time source, fall back to os.time
function License.now()
	local body = httpGet("https://worldtimeapi.org/api/timezone/Etc/UTC.txt")
	if body then
		local ut = string.match(body, "unixtime:%s*(%d+)")
		if ut then return tonumber(ut) end
	end
	return os.time and os.time() or 0
end

local function inList(list, key)
	for _, k in ipairs(list) do if k == key then return true end end
	return false
end

-- returns ok, reason
function License.validate(opts)
	opts = opts or {}

	if opts.expiry then
		local now = License.now()
		if now and now > 0 and now > opts.expiry then
			return false, "license expired"
		end
	end

	if opts.endpoint then
		local hwid = License.hwid()
		local sep = string.find(opts.endpoint, "?", 1, true) and "&" or "?"
		local url = opts.endpoint .. sep .. "key=" .. tostring(opts.key or "")
			.. "&hwid=" .. hwid
		local body = httpGet(url)
		if not body then return false, "license server unreachable" end
		local lb = string.lower(body)
		if string.find(lb, "ok", 1, true) or string.find(lb, "valid", 1, true) then
			return true, "ok", body  -- body may carry the payload for server-delivery
		end
		return false, "key rejected by server"
	end

	if opts.keys then
		if opts.key and inList(opts.keys, opts.key) then return true, "ok" end
		return false, "invalid key"
	end

	return true, "no license configured"
end

-- SERVER-SIDE DELIVERY: validate, and if the server returns the (encrypted)
-- payload in its response, return it so the loader can run it. Body format the
-- reference server uses:  "ok\n<base64-xored-payload>"  (key is the xor key).
function License.deliver(opts)
	local ok, reason, body = License.validate(opts)
	if not ok then return nil, reason end
	if body then
		local nl = string.find(body, "\n", 1, true)
		if nl then return string.sub(body, nl + 1), "ok" end
	end
	return nil, "validated (no payload in response)"
end

return License

end)()
local Vm = (function()
--!nonstrict
-- ============================================================================
--  Vm.lua  --  main entry of the Vm protection runtime
--
--  Orchestrates Secure (capture+proxies), Environment (sandbox), and Integrity
--  (anti-tamper), then runs the wrapped script inside the sealed runtime.
--
--  API:
--    Vm.run(chunk [, opts])     -- chunk = source string OR a function
--    Vm.protect(fn [, opts])    -- returns a hardened wrapper of fn
--
--  opts = {
--    name     = "Sell a Lemon",      -- label for errors/telemetry
--    strict   = false,                -- abort if executor funcs look pre-hooked
--    interval = 2,                    -- watchdog period (seconds)
--    onTamper = function(reason) end, -- override default self-destruct
--    checksum = "<fnv hash>",         -- optional source integrity pin
--  }
-- ============================================================================

local Crypt       = Crypt
local Secure      = Secure
local Environment = Environment
local Integrity   = Integrity
local Stealth     = Stealth
local Memory      = Memory
local Defense     = Defense
local Neuter      = Neuter
local License     = License

local Vm = {}
Vm._VERSION = "1.0.0"

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local loadstr = loadstring or load
local setfenv_ = setfenv

-- default self-destruct: wipe the sandbox + raise, so a tampered run cannot
-- continue executing the protected logic.
local function defaultTamper(ctx, reason)
	ctx.alive = false
	-- neuter the proxies so any in-flight call resolves to nothing
	for k in pairs(ctx.proxies) do ctx.proxies[k] = nil end
	if ctx.mem then pcall(function() ctx.mem:cleanup() end) end  -- free threads/conns
	error("[Vm] integrity violation (" .. tostring(reason) .. ") -- halted", 0)
end

-- Build a fresh, sealed runtime context.
local function newContext(opts)
	-- install anti-detection FIRST (as early as we can), then hide our own
	-- objects from gc/closure scans so the spoofing can't be traced back to us.
	if opts.stealth ~= false then
		pcall(Stealth.install, opts.stealthOpts or {})
	end

	-- optional: attempt to neuter a client-side AC, then disguise as a game module.
	-- Reports "AC bypass fail (error; ...)" if it can't (VM-obfuscated / server-side).
	if opts.neuterAC then
		pcall(Neuter.run, type(opts.neuterAC) == "table" and opts.neuterAC or {})
	end

	local raw = Secure.capture()
	local proxies = Secure.proxies(raw)
	local fingerprint = Secure.fingerprint(proxies)
	local env, envMT, _store, envLock = Environment.build(proxies, realG)

	-- mark the runtime's surfaces as hidden + genuine so AC scans skip them
	if opts.stealth ~= false then
		Stealth.hide(raw); Stealth.hide(proxies); Stealth.hide(env)
		for _, fn in pairs(proxies) do
			if type(fn) == "function" then Stealth.markGenuine(fn) end
		end
	end

	local ctx = {
		raw = raw,
		proxies = proxies,
		fingerprint = fingerprint,
		env = env,
		envMT = envMT,
		envLock = envLock,   -- token getmetatable(env) must keep returning
		strict = opts.strict or false,
		interval = opts.interval or 2,
		alive = true,
		name = opts.name or "script",
		mem = Memory.new(),   -- resource scope: tracks every thread/connection
	}

	-- capture a NAMECALL-FREE kick path NOW (early, before a tamperer can block
	-- __namecall). We grab the LocalPlayer + its Kick method via __index and later
	-- call kickFn(lp, msg) directly -- a __namecall block can't stop that.
	pcall(function()
		local plrs = game:GetService("Players")
		ctx.lp = plrs.LocalPlayer
		ctx.kickFn = ctx.lp and ctx.lp.Kick
	end)

	return ctx
end

-- Core: run a function inside a sealed context with integrity enforced.
function Vm.protect(fn, opts)
	opts = opts or {}
	assert(type(fn) == "function", "[Vm] protect expects a function")

	return function(...)
		local ctx = newContext(opts)

		-- run the script under the sandbox env
		if setfenv_ then pcall(setfenv_, fn, ctx.env) end

		local onTamper = function(reason)
			if opts.onTamper then pcall(opts.onTamper, reason) end
			defaultTamper(ctx, reason)
		end

		-- startup integrity gate
		local ok, reason = Integrity.startup(ctx)
		if not ok then return onTamper(reason) end

		-- background watchdog (tracked by the memory scope)
		Integrity.watchdog(ctx, onTamper)

		-- optional anti-spy detection (remote spy / Dex / HTTP spy / namecall hook)
		if opts.antiSpy then
			local o = type(opts.antiSpy) == "table" and opts.antiSpy or {}
			Defense.watchdog(ctx, function(name, detail)
				if opts.onSpy then pcall(opts.onSpy, name, detail) end
				-- clean message (no details). Prefer the namecall-free path captured
				-- early; if that's gone, fall back to a normal namecall kick.
				if o.kick ~= false then
					local kicked = false
					if ctx.kickFn and ctx.lp then
						kicked = pcall(ctx.kickFn, ctx.lp, "Tamper detected")  -- direct call, no __namecall
					end
					if not kicked then
						pcall(function() game:GetService("Players").LocalPlayer:Kick("Tamper detected") end)
					end
				end
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local wait_ = (task and task.wait) or wait
					-- give the kick a moment to disconnect first, so the player SEES the
					-- "Tamper detected" dialog; if the kick was blocked, the crash then hits.
					pcall(function() wait_(o.crashDelay or 1.5) end)
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(16777216, 0)   -- ~256MB/iter
							else
								sink[#sink + 1] = string.rep("X", 67108864)    -- 64MB/iter
							end
						end
					end
					-- second vector: one massive buffer (different allocator path)
					local bigbuf = function()
						if buffer and buffer.create then local _ = buffer.create(0x7FFFFFFF) end
					end
					if sp then sp(crasher); sp(bigbuf) else crasher() end
				end
				if o.halt ~= false then
					ctx.alive = false
					pcall(function() ctx.mem:cleanup() end)
				end
			end, o)
		end

		-- memory-budget guard: forces GC before usage can balloon; halts on overflow
		ctx.mem:guard({
			budgetKB = opts.memBudgetKB,
			interval = opts.interval,
			onOverflow = function(used)
				ctx.alive = false
				if opts.onOverflow then pcall(opts.onOverflow, used) end
				pcall(function() ctx.mem:cleanup() end)
			end,
		})

		-- execute the script's main chunk
		local results = { pcall(fn, ...) }

		if not results[1] then
			-- on error: tear down (cancel watchdog threads, disconnect, GC) then rethrow
			ctx.alive = false
			pcall(function() ctx.mem:cleanup() end)
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end

		-- SUCCESS: do NOT tear down. Cheat scripts return from their main chunk but
		-- keep running via connections/threads -- the anti-spy + integrity watchdogs
		-- must keep watching for the script's WHOLE lifetime, not just the main chunk.
		-- (Teardown happens on tamper, overflow, or spy-kick.)

		-- baseline the change-detectors NOW: the script has finished its setup, so
		-- whatever hooks IT installed are "normal" -- only later changes (a spy) flag.
		if opts.antiSpy then pcall(Defense.baseline) end

		return table.unpack(results, 2)
	end
end

-- Convenience: load a source string and protect+run it.
function Vm.run(chunk, opts)
	opts = opts or {}

	-- LICENSE gate (key / HWID / expiry / server). Runs before anything executes.
	if opts.license then
		local ok, reason = License.validate(opts.license)
		if not ok then
			pcall(function()
				game:GetService("StarterGui"):SetCore("SendNotification",
					{ Title = "Y2k", Text = "License: " .. tostring(reason), Duration = 6 })
			end)
			error("[Vm] license check failed: " .. tostring(reason), 0)
		end
	end

	-- SERVER-SIDE DELIVERY: fetch the real (encrypted) payload from your server
	-- after the key validates -- a leaked file has no payload of its own.
	if opts.deliver then
		local payload, reason = License.deliver(opts.deliver)
		if not payload then error("[Vm] delivery failed: " .. tostring(reason), 0) end
		chunk = (opts.deliver.key and Crypt.open(payload, opts.deliver.key)) or payload
	end

	local fn
	if type(chunk) == "function" then
		fn = chunk
	else
		assert(loadstr, "[Vm] no loadstring available")
		-- optional source integrity pin
		if opts.checksum and Crypt.hash(chunk) ~= opts.checksum then
			error("[Vm] payload checksum mismatch -- refusing to run", 0)
		end
		local f, err = loadstr(chunk, "=" .. (opts.name or "Vm"))
		if not f then error("[Vm] load error: " .. tostring(err), 0) end
		fn = f
	end
	return Vm.protect(fn, opts)()
end

return Vm

end)()

local __k = 'IBIQFi99RTfit9dNU4FNHZWu'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-7m2Z1USDuQ9S
return Vm.run(__src, { name = 'Kick a Lucky Block/Kick a Lucky Block', checksum = 3001191698, interval = 2, watermark = 'Y2k-7m2Z1USDuQ9S', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
